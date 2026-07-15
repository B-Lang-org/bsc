module DefProp(
        DefProp(..),
        defPropsHasNoCSE
        ) where

import Eval(NFData(..), rnf)
import PPrint
import Id(Id)

-- ========================================================================
-- DefProp (module def pragmas)
--
-- DefProp lives in its own module (rather than in Pragma, with the
-- other pragma types) so that it can carry ITypes: IType's module (via
-- CType) imports Pragma, so Pragma itself can never mention IType.

data DefProp
  = DefP_Rule Id   -- for method predicates
  | DefP_Method Id -- for method predicates
  | DefP_Instance Id  -- for method predicates
  | DefP_NoCSE -- indicate this def should never be used for CSE
  deriving (Eq, Ord, Show)

instance PPrint DefProp where
  pPrint _d _i = text . show

instance NFData DefProp where
  rnf (DefP_Rule x) = rnf x
  rnf (DefP_Instance x) = rnf x
  rnf (DefP_Method x) = rnf x
  rnf DefP_NoCSE = ()

-- --------------------

defPropsHasNoCSE :: [DefProp] -> Bool
defPropsHasNoCSE = elem DefP_NoCSE

-- ========================================================================
