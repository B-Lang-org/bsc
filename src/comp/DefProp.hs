module DefProp(
        DefProp(..),
        defPropsHasNoCSE,
        defPropsDictEvidence
        ) where

import Eval(NFData(..), rnf)
import PPrint
import Id(Id)
import IType(IType)

-- ========================================================================
-- DefProp (module def pragmas)
--
-- DefProp lives in its own module (rather than in Pragma, with the
-- other pragma types) because the lifted-dictionary properties below
-- carry ITypes, and IType's module (via CType) imports Pragma; Pragma
-- itself can therefore never mention IType.

data DefProp
  = DefP_Rule Id   -- for method predicates
  | DefP_Method Id -- for method predicates
  | DefP_Instance Id  -- for method predicates
  | DefP_NoCSE -- indicate this def should never be used for CSE
  -- The evidence identity of a lifted dictionary (LiftDicts), used by
  -- FixupDefs to deduplicate lifted dictionaries across packages.  The
  -- three properties are written together, at lift time, and only when
  -- the evidence is coherent and renderable:
  | DefP_DictRendering String
      -- ^ slot-normalized rendering of the dictionary's own evidence
      -- level: an injective string in which references to other lifted
      -- dictionaries appear as position markers (D0, D1, ...) into the
      -- kid list, and types appear as position markers (T0, T1, ...)
      -- into the type list
  | DefP_DictKids [Id]
      -- ^ the lifted dictionaries the evidence references, in slot order
  | DefP_DictTypes [IType]
      -- ^ the types the evidence references, in slot order
  deriving (Eq, Ord, Show)

instance PPrint DefProp where
  pPrint _d _i = text . show

instance NFData DefProp where
  rnf (DefP_Rule x) = rnf x
  rnf (DefP_Instance x) = rnf x
  rnf (DefP_Method x) = rnf x
  rnf DefP_NoCSE = ()
  rnf (DefP_DictRendering s) = rnf s
  rnf (DefP_DictKids ks) = rnf ks
  rnf (DefP_DictTypes ts) = rnf ts

-- --------------------

defPropsHasNoCSE :: [DefProp] -> Bool
defPropsHasNoCSE = elem DefP_NoCSE

-- The evidence identity of a lifted dictionary, if it has one: the
-- slot-normalized rendering, the referenced lifted dictionaries (in
-- slot order), and the referenced types (in slot order).  A dictionary
-- without a rendering (incoherent, or evidence outside the renderable
-- shapes) is never deduplicated across packages.
defPropsDictEvidence :: [DefProp] -> Maybe (String, [Id], [IType])
defPropsDictEvidence props =
    case [ s | DefP_DictRendering s <- props ] of
      [s] -> Just (s,
                   concat [ ks | DefP_DictKids ks <- props ],
                   concat [ ts | DefP_DictTypes ts <- props ])
      _ -> Nothing

-- ========================================================================
