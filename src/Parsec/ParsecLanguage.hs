-----------------------------------------------------------------------------
-- |
-- Module      :  ParsecLanguage
-- Copyright   :  (c) Daan Leijen 1999-2001
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  daan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  non-portable (uses non-portable module ParsecToken)
--
-- A helper module that defines some language definitions that can be used
-- to instantiate a token parser (see "ParsecToken").
--
-----------------------------------------------------------------------------

module ParsecLanguage
                     ( haskellDef, haskell
                     , mondrianDef, mondrian

                     , emptyDef
                     , haskellStyle
                     , javaStyle
                     , LanguageDef (..)
                     ) where
import Parsec
import ParsecToken


-----------------------------------------------------------
-- Styles: haskellStyle, javaStyle
-----------------------------------------------------------
haskellStyle :: LanguageDef st
haskellStyle= emptyDef
                { commentStart   = "{-"
                , commentEnd     = "-}"
                , commentLine    = "--"
                , nestedComments = True
                , identStart     = letter
                , identLetter	 = alphaNum <|> oneOf "_'"
                , opStart	 = opLetter haskellStyle
                , opLetter	 = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , reservedOpNames= []
                , reservedNames  = []
                , caseSensitive  = True
                }

javaStyle  :: LanguageDef st
javaStyle   = emptyDef
		{ commentStart	 = "/*"
		, commentEnd	 = "*/"
		, commentLine	 = "//"
		, nestedComments = True
		, identStart	 = letter
		, identLetter	 = alphaNum <|> oneOf "_'"		
		, reservedNames  = []
		, reservedOpNames= []	
                , caseSensitive  = False				
		}

-----------------------------------------------------------
-- minimal language definition
-----------------------------------------------------------
emptyDef   :: LanguageDef st
emptyDef    = LanguageDef
               { commentStart   = ""
               , commentEnd     = ""
               , commentLine    = ""
               , nestedComments = True
               , identStart     = letter <|> char '_'
               , identLetter    = alphaNum <|> oneOf "_'"
               , opStart        = opLetter emptyDef
               , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
               , reservedOpNames= []
               , reservedNames  = []
               , caseSensitive  = True
               }



-----------------------------------------------------------
-- Haskell
-----------------------------------------------------------
haskell :: TokenParser st
haskell      = makeTokenParser haskellDef

haskellDef  :: LanguageDef st
haskellDef   = haskell98Def
	        { identLetter	 = identLetter haskell98Def <|> char '#'
	        , reservedNames	 = reservedNames haskell98Def ++
    				   ["foreign","import","export","primitive"
    				   ,"_ccall_","_casm_"
    				   ,"forall"
    				   ]
                }
			
haskell98Def :: LanguageDef st
haskell98Def = haskellStyle
                { reservedOpNames= ["::","..","=","\\","|","<-","->","@","~","=>"]
                , reservedNames  = ["let","in","case","of","if","then","else",
                                    "data","type",
                                    "class","default","deriving","do","import",
                                    "infix","infixl","infixr","instance","module",
                                    "newtype","where",
                                    "primitive"
                                    -- "as","qualified","hiding"
                                   ]
                }


-----------------------------------------------------------
-- Mondrian
-----------------------------------------------------------
mondrian :: TokenParser st
mondrian    = makeTokenParser mondrianDef

mondrianDef :: LanguageDef st
mondrianDef = javaStyle
		{ reservedNames = [ "case", "class", "default", "extends"
				  , "import", "in", "let", "new", "of", "package"
				  ]	
                , caseSensitive  = True				
		}

				
