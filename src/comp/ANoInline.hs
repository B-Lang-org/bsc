module ANoInline (aNoInline) where

import Util(itos)
import Position(noPosition)
import Flags(Flags)
import Id(mkId, getIdBaseString)
import FStringCompat(mkFString)
import Control.Monad.State
import qualified Data.Map as M
import ASyntax
import ASyntaxUtil(mapMAExprs)
import SignalNaming


-- ===============
-- Naming conventions

-- new defs generated in this stage will be named "<aNoInlinePref><#>"
aNoInlinePref :: String
aNoInlinePref = "__f"

-- instances of noinline functions will be named with this prefix
instPrefix :: String
instPrefix = "instance_"

-- ===============
-- State for the Monad

data NIState = NIState {
    -- unique name generator
    nis_uniqueId :: Integer,
    -- definitions processed so far
    nis_defs     :: [ADef],
    -- reverse lookup of defs processed or added so far,
    -- to avoid creating new ids for the exprs which already have ids
    nis_rlookup  :: M.Map (AExpr,AType) AId
  }

-- Monad type
type NIStateMonad a = State NIState a

-- Monad Util
-- Adds a processed def
addDef :: ADef -> NIStateMonad ()
addDef newdef@(ADef i t e _) = do
           state <- get
           olddefs <- gets nis_defs
           rlm <- gets nis_rlookup
           let rlm1 = M.insert (e,t) i rlm
           put (state { nis_defs = (newdef:olddefs), nis_rlookup = rlm1 })

-- Generates a new Id from the expression to give to it
-- (This is only ever used for ANoInlineFunCall, so it need not be so general.)
genIdFromAExpr :: AExpr -> NIStateMonad AId
genIdFromAExpr expr = do
    state <- get
    uniqueNum <- gets nis_uniqueId
    put (state { nis_uniqueId = uniqueNum + 1 })
    let newIdStr = signalNameFromAExpr expr ++ aNoInlinePref ++ itos uniqueNum
    return $ mkId
               noPosition -- XXX aexpr should have an instance of HasPosition
               (mkFString newIdStr)

-- Add the expression -- really the definition to the monad
addExpr :: AType -> AExpr -> NIStateMonad AId
addExpr t e = do
    ds <- gets nis_defs
    rlm <- gets nis_rlookup
    case ( M.lookup (e,t) rlm ) of
        Nothing ->
            do
              nid <- genIdFromAExpr e
              addDef (ADef nid t e [])
              return nid
        -- don't create a new id for an expression that already has an id
        Just fid -> return fid


-- ===============
-- aNoInline

-- Make sure all no-inline functions are top-level defs,
-- and give each call an instance name (recording it in the AExpr)
-- so that all backends use the same instance name

aNoInline :: Flags -> APackage -> APackage
aNoInline flags apkg =
    let
        -- initial state
        initState = NIState {
                              nis_uniqueId = 1,
                              nis_defs = [],
                              nis_rlookup = M.empty
                            }

        -- fields of the package
        ifc = apkg_interface apkg
        rs = apkg_rules apkg
        insts = apkg_state_instances apkg
        defs = apkg_local_defs apkg

        -- monadic action
        action = do
          -- we can't use mapAExprs in one go over the whole package
          -- because we don't want to lift exprs at the top level of defs.
          -- instead, by parts:

          -- map over the defs
          -- (this doesn't return defs, it adds them all to the state,
          -- to be retrieved at the end)
          mapM_ liftADef defs

          -- map over ifcs
          ifc' <- mapMAExprs (liftAExpr False) ifc
          -- map over rules
          rs' <- mapMAExprs (liftAExpr False) rs
          -- map over state
          insts' <- mapMAExprs (liftAExpr False) insts

          -- get back the final list of defs
          -- (original defs with lifting, plus any new defs)
          defs' <- gets nis_defs

          -- now that all ANoInlineFunCall are top-level defs,
          -- assign instance names to each one
          let defs'' = updateNoInlineDefs defs'

          -- return the new package
          return (apkg { apkg_interface = ifc',
                         apkg_rules = rs',
                         apkg_state_instances = insts',
                         apkg_local_defs = defs'' })
    in
        evalState action initState


-- ===============

-- This doesn't return the defs, because they are returned via the monad
liftADef :: ADef -> NIStateMonad ()
liftADef (ADef i t e p) = do
    -- Top level case does not need to be pulled out
    e' <- liftAExpr True e
    addDef (ADef i t e' p)

-- "top" is whether the expression is the top of an ADef
-- (and therefore should not be lifted)
liftAExpr :: Bool -> AExpr -> NIStateMonad AExpr
liftAExpr False (ANoInlineFunCall t i f es) = do
    es' <- mapM (liftAExpr False) es
    i <- addExpr t (ANoInlineFunCall t i f es')
    return (ASDef t i)
-- anything else, just recurse
liftAExpr True (ANoInlineFunCall t i f es) = do
    es' <- mapM (liftAExpr False) es
    return $ ANoInlineFunCall t i f es'
liftAExpr _ (APrim aid ty op es) =  do
    es' <- mapM (liftAExpr False) es
    return $ APrim aid ty op es'
liftAExpr _ (AMethCall ty aid mid es) = do
    es' <- mapM (liftAExpr False) es
    return $ AMethCall ty aid mid es'
liftAExpr _ (AFunCall ty aid fun isC es) = do
    es' <- mapM (liftAExpr False) es
    return $ AFunCall ty aid fun isC es'
liftAExpr _ expr = return expr

-- ===============

updateNoInlineDefs :: [ADef] -> [ADef]
updateNoInlineDefs defs =
    let
        updateDef :: ADef -> (Integer, [ADef]) -> (Integer, [ADef])
        updateDef (ADef di dt (ANoInlineFunCall ft fi f es) props) (n, ds) =
            let (ANoInlineFun m ts ps _) = f
                inst_name = instPrefix ++ getIdBaseString fi ++ "_" ++ itos n
                f' = (ANoInlineFun m ts ps (Just inst_name))
                d' = (ADef di dt (ANoInlineFunCall ft fi f' es) props)
            in  (n+1, d':ds)
        updateDef d (n, ds) = (n, d:ds)
    in
        snd $ foldr updateDef (0,[]) defs

-- ===============
