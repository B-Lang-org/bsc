module VStableRenumber(stableRenumberVProgram) where

import Data.Char(isDigit, ord)
import Data.List(foldl', dropWhileEnd)
import Data.Maybe(listToMaybe, mapMaybe)
import Data.Word(Word64)
import qualified Data.Map as M
import qualified Data.Set as S

import Id(setIdBaseString)
import Util(hashInit, nextHashByte, hashValue)
import Verilog

-- Under -stable-verilog, renumber the compiler-generated name families
--
--     <stem>___dN   (backend def temporaries)
--     <stem>__hN    (elaboration heap ids, minted into the .ba)
--     <stem>__qN    (Verilog-quirks temporaries)
--     <stem>__fN    (ANoInline instance-connection wires)
--     _dmN          (AOpt-minted, whole name, no stem)
--     _dsN          (Synthesize-minted, whole name, no stem)
--
-- per module, by order of first occurrence in the emitted structure,
-- so the numbers are a pure function of the module's contents rather
-- than of mint order.  Mint order varies with compile history (the
-- heap ids arrive in the .ba with their elaboration-time numbers, and
-- the backend counters run in traversal order), so without this pass
-- two compiles that agree on structure can still disagree on N.
--
-- Soundness:
--  * Renaming is a per-module simultaneous substitution.  A target
--    name <stem><marker><k> can only collide with another family
--    member -- any name matching the pattern is itself in the map --
--    and family members all move at once.  Targets that would collide
--    with a non-renameable name (below) are skipped over.
--  * Names in non-renameable positions are never collected and never
--    produced as targets: the module's own name, everything in the
--    port list, instantiated module names, instance names, and the
--    formal port/parameter keys of instantiations (they belong to the
--    child module).  If a family-shaped name also occurs in such a
--    position (a user port named x__h5), the whole name is left
--    untouched to avoid capture.
--  * This runs before removeDollarsFromVerilog; generated family
--    names never contain '$', so the passes are disjoint.
--
-- The traversals below are written out per constructor rather than
-- derived generically.  Field order must match the declaration order
-- in Verilog.hs: the numbering is the order identifiers are reached,
-- so a field visited out of order silently renumbers.  Constructors
-- are matched without a wildcard so that adding one to Verilog.hs is
-- a compile error here rather than a name that escapes the walk.

stableRenumberVProgram :: VProgram -> VProgram
stableRenumberVProgram (VProgram ms dpis cs) =
    VProgram (map renumberModule ms) dpis cs

data Family = FamD | FamH | FamQ | FamF | FamDM | FamDS
    deriving (Eq, Ord)

-- in the order matchFamily tries them; the first match wins
families :: [Family]
families = [FamD, FamH, FamQ, FamF, FamDM, FamDS]

markerText :: Family -> String
markerText FamD  = "___d"
markerText FamH  = "__h"
markerText FamQ  = "__q"
markerText FamF  = "__f"   -- ANoInline instance-connection wires
markerText FamDM = "_dm"   -- AOpt-minted names (whole name, no stem)
markerText FamDS = "_ds"   -- Synthesize-minted names (whole name, no stem)

-- whether the family's names are the bare marker plus number
-- (no stem before the marker)
stemlessOK :: Family -> Bool
stemlessOK FamDM = True
stemlessOK FamDS = True
stemlessOK _     = False

-- split a name into (stem, family) at the rightmost marker-followed-by-digits
-- suffix. The stem is built only for the family that matches.
matchFamily :: String -> Maybe (String, Family)
matchFamily s
    | null s || not (isDigit (last s)) = Nothing
    | otherwise = listToMaybe (mapMaybe try families)
  where
    rest = dropWhileEnd isDigit s
    try fam =
        let m = markerText fam
            n = length rest - length m
        in  if n >= 0 && (stemlessOK fam || n > 0) && drop n rest == m
            then Just (take n rest, fam)
            else Nothing

-- The sets and the rename map below are used for membership and lookup only,
-- so the injective transformation from String -> (Hash,String) keys is sound.
-- The hash provides fast inequality detection for long strings with common
-- prefixes, and the string comparison cost is only paid when there is a hash
-- collision.
data NameKey = NameKey !Word64 String
    deriving (Eq, Ord)

nameKey :: String -> NameKey
nameKey s = NameKey (hashName s) s

hashName :: String -> Word64
hashName = hashValue . foldl' (\h c -> nextHashByte h (fromIntegral (ord c)))
                              hashInit

-- One walk covers all three of the following using the Hit data type:
-- 1. Collect every identifier occurrence.
-- 2. Collect every foreign function name.
-- 3. Collect every system task name.
data Hit = HId VId | HForeign String

-- ---------------------------------------------------------------- collection
--
-- Accumulator-passing, with the accumulator named in every equation so that
-- every call is saturated.  Written point-free with (.) instead, each node
-- allocates a partial application per child plus a closure per composition,
-- which costs more than the intermediate lists it was meant to avoid.
-- The accumulator is never forced, so the walk still streams and costs stack
-- proportional to the depth of the tree rather than the length of the list.

hitsItems :: [VMItem] -> [Hit] -> [Hit]
hitsItems its acc = foldr hitsItem acc its

hitsItem :: VMItem -> [Hit] -> [Hit]
hitsItem (VMDecl d) acc            = hitsDecl d acc
hitsItem (VMInst m i pas pos) acc  =
    hitsId m (hitsId i (hitsParams pas (foldr hitsAssoc acc pos)))
hitsItem (VMAssign l e) acc        = hitsLV l (hitsExpr e acc)
hitsItem (VMStmt _ s) acc          = hitsStmt s acc
hitsItem (VMComment _ it) acc      = hitsItem it acc
hitsItem (VMRegGroup i _ _ it) acc = hitsId i (hitsItem it acc)
hitsItem (VMGroup _ itss) acc      = foldr hitsItems acc itss
hitsItem (VMFunction f) acc        = hitsFunction f acc

hitsAssoc :: (VId, Maybe VExpr) -> [Hit] -> [Hit]
hitsAssoc (v, me) acc = hitsId v (hitsMExpr me acc)

-- Instance parameters are positional (Left, comment plus expression) or named
-- (Right).  Only the named arm contributes identifiers of its own; the
-- positional arm's expressions still hold them.
hitsParams :: Either [(Maybe String, VExpr)] [(VId, Maybe VExpr)]
           -> [Hit] -> [Hit]
hitsParams (Left ps) acc  = foldr (\(_, e) r -> hitsExpr e r) acc ps
hitsParams (Right ps) acc = foldr hitsAssoc acc ps

hitsMExpr :: Maybe VExpr -> [Hit] -> [Hit]
hitsMExpr Nothing acc  = acc
hitsMExpr (Just e) acc = hitsExpr e acc

-- A VId carries an optional inlined-register item, which the walk enters
-- after the identifier itself.
hitsId :: VId -> [Hit] -> [Hit]
hitsId v@(VId _ _ Nothing) acc   = HId v : acc
hitsId v@(VId _ _ (Just it)) acc = HId v : hitsItem it acc

hitsFunction :: VFunction -> [Hit] -> [Hit]
hitsFunction (VFunction n mr ds s) acc =
    hitsId n (hitsMRange mr (foldr hitsDecl (hitsStmt s acc) ds))

hitsDecl :: VVDecl -> [Hit] -> [Hit]
hitsDecl (VVDecl _ mr vs) acc = hitsMRange mr (foldr hitsVar acc vs)
hitsDecl (VVDWire mr v e) acc = hitsMRange mr (hitsVar v (hitsExpr e acc))

hitsVar :: VVar -> [Hit] -> [Hit]
hitsVar (VVar v) acc     = hitsId v acc
hitsVar (VArray r v) acc = hitsRange r (hitsId v acc)

hitsMRange :: Maybe VRange -> [Hit] -> [Hit]
hitsMRange Nothing acc  = acc
hitsMRange (Just r) acc = hitsRange r acc

hitsRange :: VRange -> [Hit] -> [Hit]
hitsRange (e1, e2) acc = hitsExpr e1 (hitsExpr e2 acc)

hitsLV :: VLValue -> [Hit] -> [Hit]
hitsLV (VLId v) acc      = hitsId v acc
hitsLV (VLConcat ls) acc = foldr hitsLV acc ls
hitsLV (VLSub l e) acc   = hitsLV l (hitsExpr e acc)

hitsStmt :: VStmt -> [Hit] -> [Hit]
hitsStmt (VAt ee s) acc         = hitsEvent ee (hitsStmt s acc)
hitsStmt (Valways s) acc        = hitsStmt s acc
hitsStmt (Vinitial s) acc       = hitsStmt s acc
hitsStmt (VSeq ss) acc          = foldr hitsStmt acc ss
hitsStmt (Vcasex e as _ _) acc  = hitsExpr e (foldr hitsArm acc as)
hitsStmt (Vcase e as _ _) acc   = hitsExpr e (foldr hitsArm acc as)
hitsStmt (VAssign l e) acc      = hitsLV l (hitsExpr e acc)
hitsStmt (VAssignA l e) acc     = hitsLV l (hitsExpr e acc)
hitsStmt (Vif e s) acc          = hitsExpr e (hitsStmt s acc)
hitsStmt (Vifelse e s1 s2) acc  = hitsExpr e (hitsStmt s1 (hitsStmt s2 acc))
hitsStmt (Vdumpvars _ vs) acc   = foldr hitsId acc vs
hitsStmt (VTask t es) acc       =
    HForeign (getVIdString t) : hitsId t (foldr hitsExpr acc es)
hitsStmt (VAssert ee es) acc    = hitsEvent ee (foldr hitsExpr acc es)
hitsStmt VZeroDelay acc         = acc

hitsArm :: VCaseArm -> [Hit] -> [Hit]
hitsArm (VCaseArm es s) acc = foldr hitsExpr (hitsStmt s acc) es
hitsArm (VDefault s) acc    = hitsStmt s acc

hitsEvent :: VEventExpr -> [Hit] -> [Hit]
hitsEvent (VEEOr e1 e2) acc  = hitsEvent e1 (hitsEvent e2 acc)
hitsEvent (VEEposedge e) acc = hitsExpr e acc
hitsEvent (VEEnegedge e) acc = hitsExpr e acc
hitsEvent (VEE e) acc        = hitsExpr e acc
hitsEvent (VEEMacro _ e) acc = hitsExpr e acc

hitsExpr :: VExpr -> [Hit] -> [Hit]
hitsExpr (VEConst _) acc         = acc
hitsExpr (VEReal _) acc          = acc
hitsExpr (VEWConst v _ _ _) acc  = hitsId v acc
hitsExpr (VEUnknown _ _) acc     = acc
hitsExpr (VEString _) acc        = acc
hitsExpr (VETriConst _) acc      = acc
hitsExpr (VEUnOp v _ e) acc      = hitsId v (hitsExpr e acc)
hitsExpr (VEOp v e1 _ e2) acc    = hitsId v (hitsExpr e1 (hitsExpr e2 acc))
hitsExpr (VEVar v) acc           = hitsId v acc
hitsExpr (VEConcat es) acc       = foldr hitsExpr acc es
hitsExpr (VEIndex v e) acc       = hitsId v (hitsExpr e acc)
hitsExpr (VESelect e1 e2 e3) acc = hitsExpr e1 (hitsExpr e2 (hitsExpr e3 acc))
hitsExpr (VESelect1 e1 e2) acc   = hitsExpr e1 (hitsExpr e2 acc)
hitsExpr (VERepeat e1 e2) acc    = hitsExpr e1 (hitsExpr e2 acc)
hitsExpr (VEIf e1 e2 e3) acc     = hitsExpr e1 (hitsExpr e2 (hitsExpr e3 acc))
hitsExpr (VEFctCall f es) acc    =
    HForeign (getVIdString f) : hitsId f (foldr hitsExpr acc es)
hitsExpr (VEMacro _) acc         = acc

-- port-list identifiers, which are excluded from renaming
portIds :: [([VArg], VComment)] -> [VId]
portIds vps = [ i | (args, _) <- vps, a <- args, i <- argIds a ]
  where
    argIds (VAInput i mr)        = i : rangeIds' mr
    argIds (VAInout i mi mmr)    = i : maybe [] (: []) mi
                                     ++ maybe [] rangeIds' mmr
    argIds (VAOutput i mr)       = i : rangeIds' mr
    argIds (VAParameter i mr e) = i : rangeIds' mr ++ exprIds e
    rangeIds' = maybe [] (\(e1, e2) -> exprIds e1 ++ exprIds e2)
    exprIds e = [ v | HId v <- hitsExpr e [] ]

-- ------------------------------------------------------------------- rewrite

mapItems :: (VId -> VId) -> [VMItem] -> [VMItem]
mapItems f = map (mapItem f)

mapItem :: (VId -> VId) -> VMItem -> VMItem
mapItem f (VMDecl d)            = VMDecl (mapDecl f d)
mapItem f (VMInst m i pas pos)  = VMInst (mapId f m) (mapId f i)
                                         (mapParams f pas)
                                         (map (mapAssoc f) pos)
mapItem f (VMAssign l e)        = VMAssign (mapLV f l) (mapExpr f e)
mapItem f (VMStmt t s)          = VMStmt t (mapStmt f s)
mapItem f (VMComment c it)      = VMComment c (mapItem f it)
mapItem f (VMRegGroup i s c it) = VMRegGroup (mapId f i) s c (mapItem f it)
mapItem f (VMGroup t itss)      = VMGroup t (map (mapItems f) itss)
mapItem f (VMFunction fn)       = VMFunction (mapFunction f fn)

mapAssoc :: (VId -> VId) -> (VId, Maybe VExpr) -> (VId, Maybe VExpr)
mapAssoc f (v, me) = (mapId f v, fmap (mapExpr f) me)

mapParams :: (VId -> VId)
          -> Either [(Maybe String, VExpr)] [(VId, Maybe VExpr)]
          -> Either [(Maybe String, VExpr)] [(VId, Maybe VExpr)]
mapParams f (Left ps)  = Left [ (c, mapExpr f e) | (c, e) <- ps ]
mapParams f (Right ps) = Right (map (mapAssoc f) ps)

mapId :: (VId -> VId) -> VId -> VId
mapId f v =
    case f v of
      VId s i mitem -> VId s i (fmap (mapItem f) mitem)

mapFunction :: (VId -> VId) -> VFunction -> VFunction
mapFunction f (VFunction n mr ds s) =
    VFunction (mapId f n) (mapMRange f mr) (map (mapDecl f) ds) (mapStmt f s)

mapDecl :: (VId -> VId) -> VVDecl -> VVDecl
mapDecl f (VVDecl t mr vs) = VVDecl t (mapMRange f mr) (map (mapVar f) vs)
mapDecl f (VVDWire mr v e) = VVDWire (mapMRange f mr) (mapVar f v) (mapExpr f e)

mapVar :: (VId -> VId) -> VVar -> VVar
mapVar f (VVar v)     = VVar (mapId f v)
mapVar f (VArray r v) = VArray (mapRange f r) (mapId f v)

mapMRange :: (VId -> VId) -> Maybe VRange -> Maybe VRange
mapMRange f = fmap (mapRange f)

mapRange :: (VId -> VId) -> VRange -> VRange
mapRange f (e1, e2) = (mapExpr f e1, mapExpr f e2)

mapLV :: (VId -> VId) -> VLValue -> VLValue
mapLV f (VLId v)      = VLId (mapId f v)
mapLV f (VLConcat ls) = VLConcat (map (mapLV f) ls)
mapLV f (VLSub l e)   = VLSub (mapLV f l) (mapExpr f e)

mapStmt :: (VId -> VId) -> VStmt -> VStmt
mapStmt f (VAt ee s)         = VAt (mapEvent f ee) (mapStmt f s)
mapStmt f (Valways s)        = Valways (mapStmt f s)
mapStmt f (Vinitial s)       = Vinitial (mapStmt f s)
mapStmt f (VSeq ss)          = VSeq (map (mapStmt f) ss)
mapStmt f (Vcasex e as p l)  = Vcasex (mapExpr f e) (map (mapArm f) as) p l
mapStmt f (Vcase e as p l)   = Vcase (mapExpr f e) (map (mapArm f) as) p l
mapStmt f (VAssign l e)      = VAssign (mapLV f l) (mapExpr f e)
mapStmt f (VAssignA l e)     = VAssignA (mapLV f l) (mapExpr f e)
mapStmt f (Vif e s)          = Vif (mapExpr f e) (mapStmt f s)
mapStmt f (Vifelse e s1 s2)  = Vifelse (mapExpr f e) (mapStmt f s1)
                                       (mapStmt f s2)
mapStmt f (Vdumpvars n vs)   = Vdumpvars n (map (mapId f) vs)
mapStmt f (VTask t es)       = VTask (mapId f t) (map (mapExpr f) es)
mapStmt f (VAssert ee es)    = VAssert (mapEvent f ee) (map (mapExpr f) es)
mapStmt _ VZeroDelay         = VZeroDelay

mapArm :: (VId -> VId) -> VCaseArm -> VCaseArm
mapArm f (VCaseArm es s) = VCaseArm (map (mapExpr f) es) (mapStmt f s)
mapArm f (VDefault s)    = VDefault (mapStmt f s)

mapEvent :: (VId -> VId) -> VEventExpr -> VEventExpr
mapEvent f (VEEOr e1 e2)  = VEEOr (mapEvent f e1) (mapEvent f e2)
mapEvent f (VEEposedge e) = VEEposedge (mapExpr f e)
mapEvent f (VEEnegedge e) = VEEnegedge (mapExpr f e)
mapEvent f (VEE e)        = VEE (mapExpr f e)
mapEvent f (VEEMacro s e) = VEEMacro s (mapExpr f e)

mapExpr :: (VId -> VId) -> VExpr -> VExpr
mapExpr _ e@(VEConst _)        = e
mapExpr _ e@(VEReal _)         = e
mapExpr f (VEWConst v a b c)   = VEWConst (mapId f v) a b c
mapExpr _ e@(VEUnknown _ _)    = e
mapExpr _ e@(VEString _)       = e
mapExpr _ e@(VETriConst _)     = e
mapExpr f (VEUnOp v o e)       = VEUnOp (mapId f v) o (mapExpr f e)
mapExpr f (VEOp v e1 o e2)     = VEOp (mapId f v) (mapExpr f e1) o
                                      (mapExpr f e2)
mapExpr f (VEVar v)            = VEVar (mapId f v)
mapExpr f (VEConcat es)        = VEConcat (map (mapExpr f) es)
mapExpr f (VEIndex v e)        = VEIndex (mapId f v) (mapExpr f e)
mapExpr f (VESelect e1 e2 e3)  = VESelect (mapExpr f e1) (mapExpr f e2)
                                          (mapExpr f e3)
mapExpr f (VESelect1 e1 e2)    = VESelect1 (mapExpr f e1) (mapExpr f e2)
mapExpr f (VERepeat e1 e2)     = VERepeat (mapExpr f e1) (mapExpr f e2)
mapExpr f (VEIf e1 e2 e3)      = VEIf (mapExpr f e1) (mapExpr f e2)
                                      (mapExpr f e3)
mapExpr f (VEFctCall fn es)    = VEFctCall (mapId f fn) (map (mapExpr f) es)
mapExpr _ e@(VEMacro _)        = e

-- ------------------------------------------------------------------ the pass

renumberModule :: VModule -> VModule
renumberModule vm =
    let
        body_hits :: [Hit]
        body_hits = hitsItems (vm_body vm) []

        -- names that must not change (or be created by renaming).
        instFixed :: VMItem -> [String]
        instFixed (VMInst m i pas pos) =
            [getVIdString m, getVIdString i] ++
            either (const []) (map (getVIdString . fst)) pas ++
            map (getVIdString . fst) pos
        instFixed (VMComment _ it)      = instFixed it
        instFixed (VMRegGroup _ _ _ it) = instFixed it
        instFixed (VMGroup _ itss)      = concatMap (concatMap instFixed) itss
        instFixed _                     = []

        -- foreign linkage names must never change: the function/task
        -- names of foreign calls (DPI declarations live at file scope,
        -- outside this module walk)
        -- (a user's imported function may itself be family-shaped,
        -- e.g. import "BDPI" f__h1)
        excluded :: S.Set NameKey
        excluded = S.fromList (map nameKey (
            getVIdString (vm_name vm) :
            map getVIdString (portIds (vm_ports vm)) ++
            [ n | HForeign n <- body_hits ] ++
            concatMap instFixed (vm_body vm)))

        -- family members in order of first occurrence.
        occurrences :: [String]
        occurrences = [ getVIdString v | HId v <- body_hits ]

        -- the seen set only needs to record names that match a family shape
        firstSeen :: S.Set NameKey -> [String] -> [(String, String, Family)]
        firstSeen _ [] = []
        firstSeen seen (s : ss) =
            case matchFamily s of
              Nothing -> firstSeen seen ss
              Just (stem, fam) ->
                  let k = nameKey s
                  in  if k `S.member` seen
                      then firstSeen seen ss
                      else if k `S.member` excluded
                           then firstSeen (S.insert k seen) ss
                           else (s, stem, fam) : firstSeen (S.insert k seen) ss

        members :: [(String, String, Family)]  -- (name, stem, family)
        members = firstSeen S.empty occurrences

        -- assign numbers per family in first-occurrence order,
        -- skipping targets that collide with non-renameable names
        assign :: M.Map Family Integer -> [(String, String, Family)]
               -> [(String, String)]
        assign _ [] = []
        assign ks ((nm, stem, fam) : rest) =
            let next n = let tgt = stem ++ markerText fam ++ show n
                         in  if nameKey tgt `S.member` excluded
                             then next (n + 1)
                             else (n, tgt)
                (k, target) = next (M.findWithDefault 1 fam ks)
            in  (nm, target) : assign (M.insert fam (k + 1) ks) rest

        renames :: M.Map NameKey String
        renames = M.fromList [ (nameKey nm, tgt)
                             | (nm, tgt) <- assign M.empty members
                             , nm /= tgt ]

        subst :: VId -> VId
        subst v@(VId s i info) =
            case M.lookup (nameKey s) renames of
              Just s' -> VId s' (setIdBaseString i s') info
              Nothing -> v
    in
        if M.null renames
        then vm
        else vm { vm_body = mapItems subst (vm_body vm) }
