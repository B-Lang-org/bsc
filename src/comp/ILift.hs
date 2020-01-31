{-# LANGUAGE PatternGuards #-}
module ILift(iLift) where
import PPrint(ppReadable)
import Flags(Flags, ifLift)
import Error(ErrorHandle)
import ISyntax
import ISyntaxUtil(ieNot,
                   icNoActions, itAction, iTrue, 
                   iGetType, ieIf, ieIfx, flatAction,
                   joinActions, notIf, isTAction,
                   isTrue, isFalse, ieAndOpt, ieOrOpt,
                   iDefMap
                   )
import ITransform(iTransExpr, iTransBoolExpr)
import PreIds(idActionValue_, idAVAction_)
import Prim


-- for trace arguments
import IOUtil(progArgs)
import Util(tracep)

trace_lift = "-trace-lift" `elem` progArgs

iLift :: ErrorHandle -> Flags -> IModule a -> IModule a
iLift errh flags imod@(IModule { imod_local_defs = ds,
                                 imod_rules      = rs,
                                 imod_interface  = ifc }) =
    imod { imod_local_defs = ds', imod_rules = rs', imod_interface = ifc' }
  where ds'  = map (iLiftDef errh flags) ds
        rs'  = (iLiftRules errh flags) rs
        ifc' = map (iLiftIfc errh flags) ifc
--      itvs'? do we need to go into state vars?

-- just lift the expression inside
iLiftDef :: ErrorHandle -> Flags -> IDef a -> IDef a
iLiftDef errh flags def = iDefMap (iLiftExpr errh flags) def

-- just lift the def inside
iLiftIfc :: ErrorHandle -> Flags -> IEFace a -> IEFace a
iLiftIfc errh flags (IEFace i x maybe_e maybe_rs wp fi) =
  IEFace i x (do { (e,t) <- maybe_e ; return ((iLiftExpr errh flags e),t) })
             (do { rs <- maybe_rs ; return (iLiftRules errh flags rs) })
             wp fi

-- try lifting on action expressions
iLiftExpr :: ErrorHandle -> Flags -> IExpr a -> IExpr a
iLiftExpr errh flags e | (isTAction (iGetType e)) = iLiftActionExpr errh flags e
-- also lift on the action part of actionvalue structs
iLiftExpr errh flags (IAps f@(ICon av (ICTuple {})) ts [val_expr, act_expr])
    | (av == idActionValue_)
    = IAps f ts [val_expr, iLiftExpr errh flags act_expr]
iLiftExpr errh flags e = e

iLiftRules :: ErrorHandle -> Flags -> IRules a -> IRules a
iLiftRules errh flags (IRules sps rs) = IRules sps (map (iLiftRule errh flags) rs)

iLiftRule :: ErrorHandle -> Flags -> IRule a -> IRule a
iLiftRule errh flags r =
    r { irule_body = iLiftExpr errh flags $ irule_body r }

-- Conditional actions (an action, extracted from an if, combined
-- with an expression describing its condition)
-- this is an intermediate representation for power-lifting
-- open question: how to handle explicit ExpIfs and NoExpIfs
-- i.e. splits and nosplits
data IActionCond a = IActionCond {
                    action :: IExpr a,
                    condition :: IExpr a
                  }

-- adds an additional condition to an ActionCond
addCond :: Flags -> IExpr a -> IActionCond a -> IActionCond a
addCond flags newcond (IActionCond { action = ac, condition = c}) = 
  IActionCond { action = ac, condition = (iTransBoolExpr flags) (newcond `ieAndOpt` c)} 

-- transform an action expression into a list of conditional actions (i.e. pushing all the ifs into conditions)
condActions :: Flags -> IExpr a -> [IActionCond a]

condActions flags e = concatMap (condActions1 flags) (flatAction e)

condActions1 :: Flags -> IExpr a -> [IActionCond a]
 
-- if case (recurses using condActions to handle action lists)
condActions1 flags (IAps (ICon i (ICPrim _ PrimIf)) _ [c,t,f]) =
   let ts = condActions flags t
       fs = condActions flags f in
       (map (addCond flags c) ts) ++ (map (addCond flags ((iTransBoolExpr flags) (ieNot c))) fs)

-- base case - the action always happens
condActions1 flags e = [IActionCond { action = e, condition = iTrue }]
  
-- convert an actionCond back into an action expression     
actionCondToIExpr :: ErrorHandle -> Flags -> IActionCond a -> IExpr a
actionCondToIExpr errh flags (IActionCond { action = ac, condition = c}) =
  (fst (iTransExpr errh (ieIfx itAction ((iTransBoolExpr flags) c) ac icNoActions))) 

-- implicitly assuming action list
-- and flattens out
iLiftActionExpr :: ErrorHandle -> Flags -> IExpr a -> IExpr a
iLiftActionExpr errh flags e =
    if (ifLift flags) 
    then (joinActions (concatMap (lift1 errh flags) (flatAction e)))
    else (joinActions (flatAction e))

-- takes in an expression and produces a list of "lifted" expressions - where conditional actions are replaced with conditional
-- expressions where possible e.g. if p r:=5 else r:=7 --> r:= if p then 7 else 5
-- now implements "power lifting" - combining the same method calls together if they are in 
-- mutually exclusive if branches even if the methods are not always called
lift1 :: ErrorHandle -> Flags -> IExpr a -> [IExpr a]

-- bulk of interesting lifting happens when we find an if expression
lift1 errh flags ifexp@(IAps (ICon id (ICPrim {primOp = PrimIf, iConType = contyp})) [typ] [cunsimp, t, f]) | (isTAction typ) =
  --
  -- loopT loops through the true-arm actions
  -- parameters are lifted expressions, unliftable (true) expressions, true expressions to scan, false actions to lift against 
  let -- convert an action cond list back into an expression list - reversing for action order preservation
      -- simplify the predicate to be safe
      c = ((iTransBoolExpr flags) cunsimp)
      raclcvt acl = (reverse (map (actionCondToIExpr errh flags) acl))

      -- end up with only lifted expressions we are done and return that
      loopT lifted [] [] [] = (raclcvt lifted)
      --
      -- done scanning but have some lifted expressions, some unliftable expressions and some false expressions
      -- tack an if of the unliftable and false expressions onto the lifted expressions
      loopT lifted unlifted [] false =
          --
          -- lifted should be first because we want to put actions with broader conditions first
          -- this will mean that we will try further lifting with "better" actions first
          -- and lift this whole thing out all the way (since we go 95% anyway and I think this
          -- combines predicates usefully
          (raclcvt lifted) ++ 
          (raclcvt (map (addCond flags c) unlifted)) ++ -- true side
          (map (actionCondToIExpr errh flags) (map (addCond flags ((iTransBoolExpr flags) (ieNot c))) false)) -- false side

{- 
          [(iTransExpr 
             (IAps (ICon id (ICPrim {primOp = PrimIf, iConType = contyp})) 
                   [typ] 
                   [c, (joinActions (raclcvt unlifted)), (joinActions (map (actionCondToIExpr errh) false))])


                   -- false does not use raclcvt because it is in the original order and does not need reversing 
           )]
-}    
      -- going through the true expressions and find a module method call 
      loopT lifted unlifted (firstT@(IActionCond {action = firstTaction@(IAps expT tsT ((icsvT@(ICon _ (svT@(ICStateVar _ _)))):argsT)),
                                                     condition = firstTcond}):restT) f = 
      -- loop through the list of false actions
      -- first parameter is scanned false actions, second is false actions to scan
      

        -- done scanning the list of false actions (restF = [])
        let loopF scanned [] = loopT lifted (firstT:unlifted) restT (reverse scanned)
            --
            -- when we find a matching method call for a module lift the method call (into a joint ActionCond) 
            -- and put conditional expressions on the arguments
            -- the length check is for things like $display so we do not lift when there are different numbers of arguments
            loopF scanned ((firstF@(IActionCond {action = firstFaction@(IAps expF _ ((icsvF@(ICon _ (svF@(ICStateVar _ _)))):argsF)),
                                                 condition = firstFcond})):restF) | (expF == expT) && (svF == svT) && 
                                                                                    ((length argsT) == (length argsF)) =
              -- just make an ActionCond out of this when it matches
              -- eventual conversion back into IExpr will force simplification
              -- c is used as the predicate to determine the argument value because when c is true the T branch should be executed
              -- note that c has already been optimized so further optimization on it directly is redundant
              loopT ((IActionCond { action = (fst 
                                               (iTransExpr errh
                                                (IAps expT 
                                                      tsT 
                                                      (icsvT:[(fst (iTransExpr errh
                                                                               (ieIf (iGetType argT)
                                                                               c 
                                                                               (fst (iTransExpr errh argT))
                                                                               (fst (iTransExpr errh argF))))) | (argT, argF) <- (zip argsT argsF)])))),
                                    condition = genLiftCond flags c firstTcond firstFcond 
                                  }
                     ):lifted) 
                    unlifted 
                    restT 
                    ((reverse scanned) ++ restF)
            --
            -- otherwise keep scanning the list of false actions
            loopF scanned (firstF:restF) = loopF (firstF:scanned) restF in
        --
        -- start with the list of scanned false actions empty
              loopF [] f  

      -- ----
      -- do the same for actionvalue calls, with an additional avAction_ selector
      loopT lifted unlifted
	    (firstT@(IActionCond {action = (IAps sel@(ICon i_sel (ICSel {})) sel_ts
	                                         [firstTaction@(IAps expT tsT ((icsvT@(ICon _ (svT@(ICStateVar _ _)))):argsT))]),
                                  condition = firstTcond}):restT) f  | (i_sel == idAVAction_) = 
            -- loop through the list of false actions
            -- first parameter is scanned false actions, second is false actions to scan
            --
            -- done scanning the list of false actions (restF = [])
        let loopF scanned [] = loopT lifted (firstT:unlifted) restT (reverse scanned)
            --
            -- when we find a matching method call for a module lift the method call (into a joint ActionCond) 
            -- and put conditional expressions on the arguments
            -- the length check is for things like $display so we do not lift when there are different numbers of arguments
            loopF scanned ((firstF@(IActionCond {action = IAps sel@(ICon i_sel (ICSel {})) sel_ts
                                                               [firstFaction@(IAps expF _ ((icsvF@(ICon _ (svF@(ICStateVar _ _)))):argsF))],
                                                 condition = firstFcond})):restF) | (i_sel == idAVAction_) &&
  		  	                 	                                    (expF == expT) && (svF == svT) && 
                                                                                    ((length argsT) == (length argsF)) =
              -- just make an ActionCond out of this when it matches
              -- eventual conversion back into IExpr will force simplification
              -- c is used as the predicate to determine the argument value because when c is true the T branch should be executed
              -- note that c has already been optimized so further optimization on it directly is redundant
              loopT ((IActionCond { action = IAps sel sel_ts
                                             [(fst 
                                               (iTransExpr errh
                                                (IAps expT 
                                                      tsT 
                                                      (icsvT:[(fst (iTransExpr errh
                                                                               (ieIf (iGetType argT) 
                                                                               c 
                                                                               (fst (iTransExpr errh argT))  
                                                                               (fst (iTransExpr errh argF))))) | (argT, argF) <- (zip argsT argsF)]))))],
                                    condition = genLiftCond flags c firstTcond firstFcond
                                  }
                     ):lifted) 
                    unlifted 
                    restT 
                    ((reverse scanned) ++ restF)
            --
            -- otherwise keep scanning the list of false actions
            loopF scanned (firstF:restF) = loopF (firstF:scanned) restF in
              --
              -- start with the list of scanned false actions empty
              loopF [] f  
              -- ----

      -- catch-all case: didn't match so can't be lifted
      loopT lifted unlifted (firstT:restT) f = loopT lifted (firstT:unlifted) restT f

-- extra lifting is wrong because foreign function calls must be undisturbed
-- extra lifting here (lifting identical exps even if they are not module method calls) - otherwise same loop
{-
      loopT lifted unlifted (firstT@(IActionCond {action = ftaction, condition = ftcond}):restT) f = 
        let loopF :: [IActionCond] -> [IActionCond] -> [IExpr]
            loopF scanned [] = loopT lifted (firstT:unlifted) restT (reverse scanned)
            loopF scanned (firstF@(IActionCond {action = ffaction, condition = ffcond}):restF) | (ftaction == ffaction) = 
-- just make a new actioncond out of the identified expression
-- eventual conversion into an IExpr will force simplification
                 let newliftee = IActionCond { action = ffaction, 
                                               condition = ((iTransBoolExpr flags) 
                                                             (((iTransBoolExpr flags) (c `ieAnd` ftcond)) `ieOr` 
                                                              ((iTransBoolExpr flags) (((iTransBoolExpr flags) (ieNot c)) `ieAnd` ffcond))))} in 
                     loopT (newliftee:lifted) unlifted restT ((reverse scanned) ++ restF)
            loopF scanned (firstF:restF) = loopF (firstF:scanned) restF in
              loopF [] f
-} 

  in
      tracep trace_lift ("found if: " ++ (ppReadable ifexp)) $
      let result = (loopT [] [] (concatMap (condActions flags) (concatMap (lift1 errh flags) (flatAction t))) 
                                (concatMap (condActions flags) (concatMap (lift1 errh flags) (flatAction f)))) in
        tracep trace_lift ("if lifting result: " ++ (ppReadable result)) $ result    

-- lift "through" an explicit split or nosplit
lift1 errh flags exp@(IAps (ICon id (ICPrim {primOp = p, iConType = contyp})) typs [e]) | (p == PrimExpIf) || (p == PrimNoExpIf) =
      tracep trace_lift ("found noexp or exp:" ++ (ppReadable exp)) $
      let es = (lift1 errh flags e) in
          -- can be multiple ifs in the result, so map over and be safe
          [if (notIf e') then e' else (IAps (ICon id (ICPrim {primOp = p, iConType = contyp})) typs [e']) | e' <- es ]

-- if nothing else matched there is no lifting work
lift1 errh flags e = tracep trace_lift ("default: " ++ (showTypeless e)) $ [e]


-- build the expression cond && otrue || ~cond && ofalse
-- in an optimized manner
genLiftCond :: Flags -> IExpr a -> IExpr a -> IExpr a -> IExpr a
genLiftCond flags cond otrue ofalse | isTrue otrue, isTrue ofalse = iTrue 
                                    | isTrue otrue                = cond  `ieOrOpt` ofalse
                                    | isTrue ofalse               = otrue `ieOrOpt` (ieNot cond)
                                    | isTrue cond                 = otrue 
                                    | isFalse cond                = ofalse
genLiftCond flags cond otrue ofalse = 
    (iTransBoolExpr flags) $ (cond `ieAndOpt` otrue) `ieOrOpt` ( (ieNot cond) `ieAndOpt` ofalse)
