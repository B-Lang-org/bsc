module ARemoveAssumps(aRemoveAssumps) where

import ASyntax
import ASyntaxUtil
import ErrorUtil(internalError)
import Id(getIdString)
import PPrint
import PreIds(idSvaRuntimeCheck)

-- XXX value method assumptions
-- The Bool says whether to add an SVA twin for each runtime check
aRemoveAssumps :: Bool -> APackage -> APackage
aRemoveAssumps sva = mapARules (removeAssumpRule sva)

addAssumpPred :: AExpr -> AAction -> AAction
addAssumpPred p f@(AFCall { aact_args = (c:es) }) = f'
  where f' = f { aact_args = (c':es) }
        c' = aAnd p c
addAssumpPred p t@(ATaskAction { aact_args = (c:es) }) = t'
  where t' = t { aact_args = (c':es) }
        c' = aAnd p c
-- XXX method calls are not allowed in assumptions
addAssumpPred _ a = internalError ("ARemoveAssumps.addAssumpPred unexpected: " ++ ppReadable a)

-- The runtime checks inserted by BSC (reporting R0001 and R0002) get a twin
-- with the same condition and message, which Verilog generation turns into
-- an assertion that the check never fires
svaTwin :: AAction -> [AAction]
svaTwin f@(AFCall { aact_assump = True }) =
    [f { aact_objid = idSvaRuntimeCheck,
         afcall_fun = getIdString idSvaRuntimeCheck }]
svaTwin _ = []

getAssumpActions :: Bool -> AAssumption -> [AAction]
getAssumpActions sva (AAssumption p as) = map (addAssumpPred p) (as ++ sva_as)
  where sva_as = if sva then concatMap svaTwin as else []

removeAssumpRule :: Bool -> ARule -> ARule
removeAssumpRule sva r@(ARule { arule_actions = as,
                                arule_assumps = asmps }) = r'
  where r' = r { arule_actions = as', arule_assumps = [] }
        as' = as ++ assump_actions
        assump_actions = concatMap (getAssumpActions sva) asmps

