module Pretty (module GHCPretty, pretty,
	       -- utils
	       s2par, s2docs
	      ) where

import GHCPretty

--
-- The follow definitions used to be in PPrint, but this caused a
-- dependency cycle from ErrorUtil to PPrint to Util to ErrorUtil.
-- Since ErrorUtil only needed core Pretty routines and not the PPrint
-- functionality, this module was created.
--

-- XXX old comment from PPrint: pretty and string_txt should be replaced

-- Produces a string from a text "x" in Normal mode with "w" line
-- length, "w/m" ribbons per line.
pretty :: Int -> Int -> Doc -> String
pretty w m x = fullRender PageMode w (toEnum w / toEnum m) string_txt "\n" x

-- The function which tells fullRender how to compose Doc elements
-- into a String.
string_txt (Chr c)   s  = c:s
string_txt (Str s1)  s2 = s1 ++ s2
string_txt (PStr s1) s2 = s1 ++ s2

----

-- Pretty printing utilities

-- Creates a paragraph
s2par :: String -> Doc
s2par str = fsep $ map text (words str)

-- Creates a list of Doc, to later be joined
s2docs :: String -> [Doc]
s2docs str = map text (words str)

----

