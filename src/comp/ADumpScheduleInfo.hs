-- This is a separate module for defining just the types exported by
-- ADumpSchedule.  This module can be imported by modules that need the
-- types (such as GenABin, bluetcl) without having to import ADumpSchedule
-- (which imports DisjointTest and requires linking with the SAT libraries)
--
module ADumpScheduleInfo(
		         MethodDumpInfo,
		         RuleConflictType(..)
                        ) where

import ASyntax(AId, AExpr)

-- -------------------------

type MethodDumpInfo = [(AId, AExpr,[(AId,RuleConflictType)])] 

-- rule conflict distinctions to print out
data RuleConflictType = Complete  |
                        SCBefore  |
                        SCAfter   |
                        SCBeforeR | -- restricted versions cannot be
                                    -- called in same rule 
                        SCAfterR  |
                        ConflictFree
   deriving(Eq, Enum)

instance Show RuleConflictType where
  show Complete     = "C"
  show SCBefore     = "<"
  show SCAfter      = ">"
  show SCBeforeR    = "<R"
  show SCAfterR     = ">R"
  show ConflictFree = "CF"
 
-- -------------------------

