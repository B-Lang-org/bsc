module BinParse(binop) where

import Parse
import Fixity

import ErrorUtil(internalError)


binop :: (o -> Fixity) -> -- extract operator fixity
         (a -> o -> a -> a) -> -- combine operands
         Parser t o -> -- parse operator
         Parser t a -> -- parse operand
         Parser t a
binop fix bin op atom = (atom >>- (:[])) `into` opsO []
  where opsO os as = op `into` newop os as
                 ||! succeed (end os as)
        opsA os as = atom `into` (\ a -> opsO os (a:as))
        end [] [a] = a
        end (o:os) (a:b:as) = end os (bin b o a : as)
        end _ _ = internalError "binop parse: bad operand stack"
        newop [] as iop = opsA [iop] as
        newop oos@(sop:os) as@(~(a:b:as')) iop =
	    let (iprec,iass) = prec iop
	        (sprec,sass) = prec sop
	    in  if iprec==sprec && (iass/=sass || iass==FInfix iprec) then
		failure "proper operator combination"
	    else if iprec>sprec || iprec==sprec && iass==FInfixr iprec then
		opsA (iop:oos) as
	    else
		newop os (bin b sop a : as') iop
        prec o =
	    case fix o of
	    f@(FInfixl i) -> (i, f)
	    f@(FInfixr i) -> (i, f)
	    f@(FInfix  i) -> (i, f)
            f             -> internalError("BinParse :: prec  unexpected pattern")

