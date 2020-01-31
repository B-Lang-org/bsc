module ARemoveAssumps(aRemoveAssumps) where

import ASyntax
import ASyntaxUtil
import ErrorUtil(internalError)
import PPrint

-- XXX value method assumptions
aRemoveAssumps :: APackage -> APackage
aRemoveAssumps = mapARules removeAssumpRule

addAssumpPred :: AExpr -> AAction -> AAction
addAssumpPred p f@(AFCall { aact_args = (c:es) }) = f'
  where f' = f { aact_args = (c':es) }
        c' = aAnd p c
addAssumpPred p t@(ATaskAction { aact_args = (c:es) }) = t'
  where t' = t { aact_args = (c':es) }
        c' = aAnd p c
-- XXX method calls are not allowed in assumptions
addAssumpPred _ a = internalError ("ARemoveAssumps.addAssumpPred unexpected: " ++ ppReadable a)

getAssumpActions :: AAssumption -> [AAction]
getAssumpActions (AAssumption p as) = map (addAssumpPred p) as

removeAssumpRule :: ARule -> ARule
removeAssumpRule r@(ARule { arule_actions = as,
                            arule_assumps = asmps }) = r'
  where r' = r { arule_actions = as', arule_assumps = [] }
        as' = as ++ assump_actions
        assump_actions = concatMap getAssumpActions asmps

 