module GroundCType(groundCTypeEnabled, internGroundCType,
                   isGroundNodeId, groundCTypeStats) where

import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Data.IORef(IORef, newIORef, readIORef, modifyIORef',
                  atomicModifyIORef')
import Data.List(genericLength, genericSplitAt)
import Control.Monad(foldM, when)
import System.IO.Unsafe(unsafePerformIO)
import System.Mem.StableName(StableName, makeStableName, hashStableName,
                             eqStableName)

import Id(Id, getIdBase, getIdQual)
import CType(Type(..), TyCon(..), TISort(..), splitTAp)
import TypeOps(opNumT, opStrT, isPrimTFunName)
import Pred(Instantiate(..))
import Position(noPosition)
import FStringCompat(FString)
import PreStrings(fsEmpty)

-- =====
-- Ground-CType interning
--
-- A side hash-cons table for ground types.  One bottom-up walk maps a
-- type to a small node id and to the canonical, physically shared
-- node for its normal form.  Each key is built from child ids and
-- normalized leaf names, so it costs O(1).  A consumer that needs the
-- identity of a large ground type pays one walk instead of a
-- synonym-expanding copy and a deep comparison per consultation, and
-- a consumer that retains the type can store the canonical node
-- instead of its own copy.  Canonical nodes are ordinary CTypes, and
-- callers pattern match them like any other type.  Sharing them is
-- safe because they are ground: no substitution can ever rewrite one.
--
-- The walk does three jobs at once: it rejects any type containing a
-- variable, it normalizes (expanding TItype applications as
-- Pred.expandSyn does and evaluating primitive type functions over
-- literals as its apTFun does), and it builds the key.  Equal node
-- ids therefore mean both types are ground and reduce to the same
-- synonym-free, type-function-free normal form, which is the
-- structure of the canonical node.  A StableName-keyed fast path
-- returns the entry for any object that it has already interned,
-- without descending, so a consultation on a circulating canonical
-- node costs one pointer probe.
--
-- The tables are process-global, under the same unsafePerformIO and
-- NOINLINE discipline as IType's intern table.  No substitution
-- rewrites a ground term and none of them depends on the symbol
-- table, so the tables need no invalidation and no scope tracking.
-- Node ids are arrival-order and may be used only for identity and,
-- through isGroundNodeId, for groundness.
--
-- Keys carry no positions.  An interior node is keyed on its child
-- ids, a TCon leaf on its qualifier and base name (exactly what idEq
-- compares), and a TyNum or TyStr leaf on its value.  So
-- canonicalization conflates exactly what Eq Type already conflates.
-- A canonical node keeps the positions of whichever occurrence
-- reached the table first, which is the same conflation that
-- .bo-imported types already exhibit.  A literal that comes from
-- evaluating a type function gets noPosition.  Typecheck errors
-- anchor on the position lists of VPred and PredWithPositions, which
-- live outside the type.
--
-- A type is refused (Nothing) when interning cannot establish
-- identity cheaply or cannot guarantee a symbol-table-independent
-- normal form:
--   - it contains a type variable, a TGen or a TDefMonad;
--   - a synonym is recursive or partially applied (the normal paths
--     report those; the walk declines);
--   - a primitive type function does not evaluate to a literal;
--   - it contains an associated type function (TIatf), which resolves
--     against the current symbol table's instances;
--   - a type constructor is unqualified, since identity by name needs
--     the one-tycon-per-qualified-name invariant (cf. IType.mkITCon).

-- Interning is a pure side table, so a consumer that never calls
-- internGroundCType pays nothing and there is nothing to gate.
groundCTypeEnabled :: Bool
groundCTypeEnabled = True

-- counters for the -trace-ctype-stats dump: the consultation count,
-- the pointer-fast-path hits at the root and in the walk, and the
-- number of nodes the walk visits
{-# NOINLINE cnGCTIntern #-}
cnGCTIntern :: IORef Int
cnGCTIntern = unsafePerformIO $ newIORef 0

{-# NOINLINE cnGCTRootPtrHit #-}
cnGCTRootPtrHit :: IORef Int
cnGCTRootPtrHit = unsafePerformIO $ newIORef 0

{-# NOINLINE cnGCTWalkPtrHit #-}
cnGCTWalkPtrHit :: IORef Int
cnGCTWalkPtrHit = unsafePerformIO $ newIORef 0

{-# NOINLINE cnGCTWalkNodes #-}
cnGCTWalkNodes :: IORef Int
cnGCTWalkNodes = unsafePerformIO $ newIORef 0

gctBump :: IORef Int -> IO ()
gctBump r = modifyIORef' r (+1)

-- | Counter/table snapshot for the -trace-ctype-stats dump.
groundCTypeStats :: IO [(String, Int)]
groundCTypeStats = do
    n1 <- readIORef cnGCTIntern
    n2 <- readIORef cnGCTRootPtrHit
    n3 <- readIORef cnGCTWalkPtrHit
    n4 <- readIORef cnGCTWalkNodes
    GCTState _ n <- readIORef gctState
    return [ ("gctype.intern_calls", n1)
           , ("gctype.root_ptr_hit", n2)
           , ("gctype.walk_ptr_hit", n3)
           , ("gctype.walk_nodes", n4)
           , ("gctype.table_nodes", n)
           ]

-- The identity of a child inside a table key: an interior application
-- by its node id, a leaf by its normalized name or value.  Positions,
-- kinds and sorts are excluded, since a qualified name determines its
-- tycon.  Leaf and interior ids share one namespace.
data GCTKey
        = GCTAp {-# UNPACK #-} !Int {-# UNPACK #-} !Int
        | GCTCon !FString !FString   -- qualifier, base
        | GCTNum !Integer
        | GCTStr !FString
        deriving (Eq, Ord)

-- Ids pack arrival order with a groundness bit, so identity and
-- groundness stay separate questions (see isGroundNodeId).
gctMkId :: Int -> Bool -> Int
gctMkId n grnd = 2 * n + (if grnd then 0 else 1)

-- | Canonical and ground: no TVar/TGen/TDefMonad anywhere inside the
-- node this id names, so substitution, instantiation and
-- free-variable collection are all the identity on it.  This is the
-- only test that may stand in for "has no variables inside".
isGroundNodeId :: Int -> Bool
isGroundNodeId i = i >= 0 && even i

-- One variable-bearing child makes the whole spine non-ground.  A
-- leaf that interns at all is ground: the walk refuses
-- variable-bearing leaves.
keyIsGround :: GCTKey -> Bool
keyIsGround (GCTAp k1 k2) = isGroundNodeId k1 && isGroundNodeId k2
keyIsGround _            = True

-- key -> (node id, canonical node), whose children are already
-- canonical
data GCTState = GCTState !(M.Map GCTKey (Int, Type)) {-# UNPACK #-} !Int

{-# NOINLINE gctState #-}
gctState :: IORef GCTState
gctState = unsafePerformIO $ newIORef (GCTState M.empty 0)

-- The pointer fast path holds every heap object that is known to
-- intern to an entry: every canonical interior node, and every root
-- that a caller has interned.  They are keyed by StableName and
-- bucketed on its hash.  An object is named only after it has been
-- forced to WHNF, since a thunk and its value may name differently;
-- that can cost a miss but never give a false hit.
data PtrTable = PtrTable !(IM.IntMap [(StableName Type, (Int, Type))])

{-# NOINLINE ptrTable #-}
ptrTable :: IORef PtrTable
ptrTable = unsafePerformIO $ newIORef (PtrTable IM.empty)

ptrLookup :: Type -> IO (Maybe (Int, Type))
ptrLookup t = t `seq` do
    sn <- makeStableName t
    PtrTable m <- readIORef ptrTable
    case IM.lookup (hashStableName sn) m of
      Nothing -> return Nothing
      Just bucket -> return (go sn bucket)
  where go sn ((sn', e) : rest) | eqStableName sn sn' = Just e
                                | otherwise = go sn rest
        go _ [] = Nothing

ptrInsert :: Type -> (Int, Type) -> IO ()
ptrInsert t e = t `seq` do
    sn <- makeStableName t
    atomicModifyIORef' ptrTable
        (\ (PtrTable m) ->
             (PtrTable (IM.insertWith (++) (hashStableName sn) [(sn, e)] m),
              ()))

-- the intern-table probe: the canonical candidate, whose children are
-- already canonical, is forced only if the key is new
nodeEntry :: GCTKey -> Type -> IO (Int, Type)
nodeEntry key cand = do
    GCTState m0 _ <- readIORef gctState
    case M.lookup key m0 of
      Just e  -> return e
      Nothing -> do
        (e@(_, canon), isNew) <- atomicModifyIORef' gctState go
        -- a new interior node joins the pointer fast path, so a
        -- later walk stops at it without descending
        when (isNew && isAp) $ ptrInsert canon e
        return e
  where
    isAp = case key of GCTAp _ _ -> True
                       _        -> False
    go st@(GCTState m n) =
        case M.lookup key m of
          Just e  -> (st, (e, False))
          Nothing -> let e = (gctMkId n (keyIsGround key), cand)
                     in  (GCTState (M.insert key e m) (n+1), (e, True))

-- the value view of a normalized node, for evaluating primitive type
-- functions
data GCTView = GVNum !Integer | GVStr !FString | GVOther

viewOf :: Type -> GCTView
viewOf (TCon (TyNum n _)) = GVNum n
viewOf (TCon (TyStr s _)) = GVStr s
viewOf _ = GVOther

-- | Intern a ground type, returning its node id and the canonical
-- shared node of its normal form, which is safe to store in place of
-- the argument.  The result is Nothing when the type is not ground
-- or not internable (see the module note for what is refused).
{-# NOINLINE internGroundCType #-}
internGroundCType :: Type -> Maybe (Int, Type)
internGroundCType t = unsafePerformIO $ do
    gctBump cnGCTIntern
    hit <- ptrLookup t
    case hit of
      Just e -> do gctBump cnGCTRootPtrHit
                   return (Just e)
      Nothing -> do
        r <- walk [] t
        case r of
          Just e -> do ptrInsert t e   -- re-interning this object: O(1)
                       return (Just e)
          Nothing -> return Nothing

walk :: [Id] -> Type -> IO (Maybe (Int, Type))
walk syns t0 = do
    hit <- ptrLookup t0
    case hit of
      Just e -> do gctBump cnGCTWalkPtrHit
                   return (Just e)
      Nothing -> do
        r <- walk' syns t0
        -- Memoize every object that the walk visits, not only the
        -- interned roots.  Otherwise a body that names the same
        -- synonym twice re-expands it once per path, which is
        -- exponential on synonym towers.  Refusals are not cached,
        -- since a refusal under a non-empty synonym stack does not
        -- transfer to other contexts.
        case r of
          Just e  -> ptrInsert t0 e
          Nothing -> return ()
        return r

walk' :: [Id] -> Type -> IO (Maybe (Int, Type))
walk' syns t0 = gctBump cnGCTWalkNodes >>
    let (f, as) = splitTAp t0
    in  case f of
          TCon (TyCon i _ (TItype n body))
            | i `elem` syns -> return Nothing      -- recursive synonym
            | genericLength as < n -> return Nothing  -- partial application
            | otherwise ->
                -- expand like Pred.expandSyn: substitute the first n
                -- arguments into the body, keep the rest applied
                let (as1, as2) = genericSplitAt n as
                in  walk (i:syns) (foldl TAp (inst as1 body) as2)
          TCon (TyCon _ _ (TIatf {})) -> return Nothing
          TCon tc@(TyCon i _ _)
            | isPrimTFunName i -> do
                mks <- walkArgs syns as
                case mks of
                  Nothing -> return Nothing
                  Just ks ->
                    -- evaluate like Pred.apTFun, but refuse the node
                    -- if the application does not reduce to a literal
                    case tfunVal i (map (viewOf . snd) ks) of
                      Just (Left n)  ->
                          Just <$> nodeEntry (GCTNum n)
                                             (TCon (TyNum n noPosition))
                      Just (Right s) ->
                          Just <$> nodeEntry (GCTStr s)
                                             (TCon (TyStr s noPosition))
                      Nothing        -> return Nothing
            | getIdQual i == fsEmpty -> return Nothing
            | otherwise -> do
                mks <- walkArgs syns as
                case mks of
                  Nothing -> return Nothing
                  Just ks -> do
                      e0 <- nodeEntry (GCTCon (getIdQual i) (getIdBase i))
                                      (TCon tc)
                      e  <- foldM app e0 ks
                      return (Just e)
          TCon tc@(TyNum n _) | null as -> Just <$> nodeEntry (GCTNum n) (TCon tc)
          TCon tc@(TyStr s _) | null as -> Just <$> nodeEntry (GCTStr s) (TCon tc)
          _ -> return Nothing   -- TVar/TGen/TDefMonad/ill-kinded
  where
    app (k1, c1) (k2, c2) = nodeEntry (GCTAp k1 k2) (TAp c1 c2)
    walkArgs sy ts = do
        mks <- mapM (walk sy) ts
        return (sequence mks)

tfunVal :: Id -> [GCTView] -> Maybe (Either Integer FString)
tfunVal i [GVNum x, GVNum y] = Left <$> opNumT i [x, y]
tfunVal i [GVNum x]          = Left <$> opNumT i [x]
tfunVal i [GVStr x, GVStr y] = Right <$> opStrT i [x, y]
tfunVal _ _                  = Nothing
