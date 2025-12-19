{-# LANGUAGE DeriveDataTypeable #-}
module ConTagInfo(ConTagInfo(..)) where

import Eval
import PPrint
import Data.Generics

-- Collects constructor and tag metadata for use in the symbol table and ISyntax.
--  e.g., data T = A T1 | B T2
--  A expr -> ConTagInfo { conNo = 0, numCon = 2, conTag = 0, tagSize = 1 }
--
-- conTag defaults to conNo and tagSize defaults to log2 numCon, but they can
-- be customized.
data ConTagInfo = ConTagInfo { conNo :: Integer,  -- position of constructor
                               numCon :: Integer, -- number of constructors
                               conTag :: Integer, -- tag value when packed
                               tagSize :: Integer -- bits required to represent tag
                             }
  deriving (Eq, Show, Data, Typeable)

instance NFData ConTagInfo where
    rnf (ConTagInfo x1 x2 x3 x4) = rnf4 x1 x2 x3 x4

instance PPrint ConTagInfo where
    pPrint d p cti = pparen True $ commaSep [text conStr, text tagStr]
      where str f = show $ f cti
            conStr = str conNo ++ " of " ++ str numCon
            tagStr = "tag = " ++ str conTag ++ " :: Bit " ++ str tagSize
