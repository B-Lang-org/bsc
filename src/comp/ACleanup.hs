module ACleanup(aCleanup) where
import ASyntax
import ASyntaxUtil
import Prim
import DisjointTest(DisjointTestState, initDisjointTestState,
                    addADefToDisjointTestState, checkDisjointExprWithCtx)
import Data.Maybe
import Flags(Flags)
import Control.Monad(when)
import Control.Monad.State(StateT, evalStateT, liftIO, get, put)
import FStringCompat(mkFString)
import Position(noPosition)
import Id
import Util
import IOUtil(progArgs)
import PPrint(ppReadable, ppString)
import Error(ErrorHandle)

trace_disjoint_tests :: Bool
trace_disjoint_tests = "-trace-disjoint-tests" `elem` progArgs

-- =====
-- Naming conventions

acleanupPref :: String
acleanupPref = "_dfoo"

-- =====

-- A state monad for generating identifiers and capturing definitions during the cleanup pass
data CState = CState Integer [ADef] DisjointTestState

-- Identifiers are _prefix# and the first is _prefix1
-- prefix is acleanupPref
initCState :: DisjointTestState -> CState
initCState dts = CState 1 [] dts

-- the state monad itself
type CMonad   = StateT CState IO

addDef :: ADef -> CMonad ()
addDef d = do
    (CState i ds dts) <- get
    dts' <- liftIO $ addADefToDisjointTestState dts [d]
    put (CState i (d:ds) dts')

getDefs :: CMonad [ADef]
getDefs = do
            (CState i ds dts) <- get
            return (reverse ds)

getDisjointTestState :: CMonad DisjointTestState
getDisjointTestState = do
    (CState i ds dts) <- get
    return dts

updateDisjointTestState :: DisjointTestState -> CMonad ()
updateDisjointTestState dts = do
    (CState i ds _) <- get
    put (CState i ds dts)

newName :: CMonad AId
newName = do
    (CState i ds dts) <- get
    put (CState (i+1) ds dts)
    return $ mkId noPosition (mkFString (acleanupPref ++ itos i))


aCleanup :: ErrorHandle -> Flags -> APackage -> IO APackage
aCleanup errh flags apkg = do
  let userDefs = apkg_local_defs apkg
      state = apkg_state_instances apkg
      userARules = apkg_rules apkg
      ifs = apkg_interface apkg
      -- definitions of the value methods in the interface
      ifcDefs = [d | (AIDef { aif_value = d }) <- ifs] ++
                [d | (AIActionValue { aif_value = d }) <- ifs]
  let str = "cleanup_" ++ ppString (apkg_name apkg)
  dts <- initDisjointTestState str errh flags (userDefs ++ ifcDefs) state []
  let initstate = initCState dts
  evalStateT (do
                userARules' <- mapM (cleanupRule flags Nothing) userARules
                ifs' <- mapM (cleanupIfc flags) ifs
                newDefs <- getDefs
--              traceM (show newDefs)
                let defs' = userDefs ++ newDefs
                return (apkg { apkg_local_defs = defs', apkg_rules = userARules', apkg_interface = ifs' }))
            initstate


cleanupRule :: Flags -> Maybe AExpr -> ARule -> CMonad ARule
cleanupRule flags mrdy (ARule id rps descr wp pred actions asmps splitorig) =
  do -- if the rule is the Action part of a method (possible a split method)
     -- then we need to include the method's ready condiion
     let pred' = case mrdy of
                   Nothing -> pred
                   Just rdy -> aAnd rdy pred
     actions' <- cleanupActions flags pred' actions
     -- don't cleanup assumption actions because they include no methods
     return (ARule id rps descr wp pred actions' asmps splitorig)

cleanupIfc :: Flags -> AIFace -> CMonad AIFace
cleanupIfc flags a@(AIAction { aif_pred = rdy, aif_body = rs }) =
  do rs' <- mapM (cleanupRule flags (Just rdy)) rs
     return a { aif_body = rs' }

cleanupIfc flags a@(AIActionValue { aif_pred = rdy, aif_body = rs }) =
  do rs' <- mapM (cleanupRule flags (Just rdy)) rs
     return a { aif_body = rs' }

cleanupIfc _ ifc = return ifc

-- merge mutually exclusive calls to the same action method
-- really a later pass lifting (so I suppose no-lift no longer breaks anything)
cleanupActions :: Flags -> AExpr -> [AAction] -> CMonad [AAction]
cleanupActions flags pred as =
  let
      loop :: [AAction] -> [AAction] -> CMonad [AAction]
      loop merged [] = return (reverse merged)

      -- Found an action method
      loop merged (first@(ACall id methodid (cond:args)):rest) =
         -- Internal loop to scan for matching actions that might be ME
         let loopR :: [AAction] -> [AAction] -> CMonad [AAction]
             loopR scanned [] =
                return ((reverse merged) ++ [first] ++ (reverse scanned))

         -- not necessary - rest has been cleaned already
         -- loopR scanned [] = loop (first:merged) (reverse scanned)
             loopR scanned (firstR@(ACall id' methodid' (cond':args')):restR)
                                | (id == id') &&
                                    (methodid == methodid') &&
                                    ((length args) == (length args')) =
                do
                   dtState <- getDisjointTestState
                   (isDisjoint,newstate) <-
                        liftIO $ checkDisjointCond dtState pred cond cond'
                   updateDisjointTestState newstate

                   if (isDisjoint) then
                     do
                        newid <- newName
                        addDef (ADef newid aTBool
                                (APrim newid aTBool PrimBOr [cond, cond']) [])
                        newargs <-
                            (mapM (\ (arg, arg') ->
                                do
                                    argid <- newName
                                    let argtyp = (aType arg)
                                    addDef (ADef argid argtyp
                                        (APrim argid argtyp PrimIf [cond, arg, arg']) [])
                                    return (ASDef argtyp argid))
                                         (zip args args'))
                        let newcall = (ACall id methodid
                                ((ASDef aTBool newid):newargs))

          -- restR is guaranteed merged amongst itself (see below)
          -- so no more work need be done...
                        return ((reverse merged)
                                ++ [newcall]
                                ++ (reverse scanned)
                                ++ restR)
                     else loopR (firstR:scanned) restR
             loopR scanned (firstR:restR) = loopR (firstR:scanned) restR

             -- aggressively merge the rest
             -- which allows the shortcuts in loopR above
         in do rest' <- (loop [] rest)
               (loopR [] rest')

      -- don't try to merge foreign function calls since
      -- those shouldn't get muxed anyway
      loop merged (first:rest) = loop (first:merged) rest
  in (loop [] as)


checkDisjointCond :: DisjointTestState -> AExpr -> AExpr -> AExpr ->
                     IO (Bool, DisjointTestState)
checkDisjointCond dtState pred cond1 cond2 =
    do
      (mres, dtState') <- checkDisjointExprWithCtx dtState pred pred cond1 cond2
      let res  = if isNothing mres then False else fromJust mres
      when(trace_disjoint_tests) $
          putStrLn("checkDisjoint(ACleanup)\n" ++
                   -- "pred: " ++ (ppReadable pred) ++
                   "cond1: " ++ (ppReadable cond1) ++
                   "cond2: " ++ (ppReadable cond2) ++
                   "Result: " ++ (show mres))
      return (res, dtState')
