module ADropDefs(aDropDefs) where

import ASyntax
import ASyntaxUtil
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import AConv(isLocalAId)
import Id

-- get all of the ASDef usage in a "thing"
dVars :: (AExprs a) => a -> [AId]
dVars = findAExprs dVarsE
  where dVarsE (ASDef _ i) = [i]
        dVarsE (APrim { ae_args = es }) = dVars es
        dVarsE (AMethCall { ae_args = es}) = dVars es
        dVarsE (ANoInlineFunCall { ae_args = es }) = dVars es
        dVarsE (AFunCall { ae_args = es }) = dVars es
        dVarsE _ = []

aDropDefs aspkg = aspkg { aspkg_values = defs' }
  where roots = dVars (aspkg_state_instances aspkg) ++
                map fst (aspkg_outputs aspkg) ++
                dVars (aspkg_foreign_calls aspkg) ++
                aspkg_inlined_ports aspkg ++
                fires ++ meth_ids ++ unusedKeeps
        unusedKeeps = [i | ADef i _ e _ <- defs, 
                       hasIdProp i IdP_keepEvenUnused
                       || isKeepId i
                         ]
        defs  = aspkg_values aspkg
        dmap  = M.fromList [(i, dVars e) | ADef i _ e _ <- defs ]
        used  = execState (mapM_ (addUsed dmap) roots) S.empty
        -- isKeepId must be in the roots or else it can result in a
        -- parent getting kept but not a child.
        keepId i | isKeepId i = True
        keepId i | isLocalAId i = i `S.member` used
        keepId i = True
        fires = [ i | d@(ADef i _ _ _) <- defs, isFire i]
        meth_ids = [i | d@(ADef i _ _ _) <- defs, isMethId i]
        defs' = [ d | d@(ADef i _ _ _) <- defs, keepId i]

addUsed :: M.Map AId [AId] -> AId -> State (S.Set AId) ()
addUsed dmap i = do
  s <- get
  if (i `S.member` s) then return ()
   else do put (S.insert i s)
           let is = M.findWithDefault [] i dmap
           mapM_ (addUsed dmap) is
