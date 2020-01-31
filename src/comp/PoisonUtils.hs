module PoisonUtils where

-- utilities for generating and working with "poisoned" definitions

import Id
import PreIds
import CSyntax

mkPoisonedCDefn :: Id -> CQType -> CDefn
mkPoisonedCDefn i cqt = CValueSign (CDef i cqt [body])
  where body = CClause [] [] (CApply (CVar idPrimPoisonedDef) [name_expr])
        name_expr = CApply (CVar idPrimGetName) [CVar i]