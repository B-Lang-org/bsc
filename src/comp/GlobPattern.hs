module GlobPattern (parseGlobPattern, matchGlobPattern, getGlobErr,
                    GlobPattern, GlobFn) where

import Control.Monad(msum)
import Data.List(isPrefixOf, tails)

-- import Debug.Trace

data CharClass = CharRange Char Char
               | CharList [Char]
               | BadCharClass String
  deriving (Eq)

instance Show CharClass where
  show (CharRange lo hi) = [lo,'-',hi]
  show (CharList cs) = cs
  show (BadCharClass s) = "<BADCHARCLASS: " ++ s ++ ">"

data GlobPattern = GlobEnd
                 | GlobMatch String GlobPattern
                 | GlobOneChar GlobPattern
                 | GlobAnyChars GlobPattern
                 | GlobOneOf [CharClass] GlobPattern
                 | GlobNotOneOf [CharClass] GlobPattern
                 | GlobBadPattern String
  deriving (Eq)

instance Show GlobPattern where
  show GlobEnd = ""
  show (GlobMatch s p) = s ++ (show p)
  show (GlobOneChar p) = "?" ++ (show p)
  show (GlobAnyChars p) = "*" ++ (show p)
  show (GlobOneOf cs p) = "[" ++ (concatMap show cs) ++ "]" ++ (show p)
  show (GlobNotOneOf cs p) = "[!" ++ (concatMap show cs) ++ "]" ++ (show p)
  show (GlobBadPattern s) = "<BADPATTERN: " ++ s ++ ">"

type GlobFn = String -> Bool

globSeparator = '.'

-- Parse a string into a GlobPattern
parseGlobPattern :: String -> GlobPattern
parseGlobPattern "" = GlobEnd
parseGlobPattern ('*':rest) = GlobAnyChars (parseGlobPattern rest)
parseGlobPattern ('?':rest) = GlobOneChar (parseGlobPattern rest)
parseGlobPattern ('[':'!':rest) = 
    let (cs,xs) = parseCharClasses rest
    in case (msum (map getClassErr cs)) of
         (Just err) -> GlobBadPattern err
         Nothing    -> GlobNotOneOf cs (parseGlobPattern xs)
parseGlobPattern ('[':rest) = 
    let (cs,xs) = parseCharClasses rest
    in case (msum (map getClassErr cs)) of
         (Just err) -> GlobBadPattern err
         Nothing    -> GlobOneOf cs (parseGlobPattern xs)
parseGlobPattern ['\\'] = GlobBadPattern $ "escape character ends pattern"
parseGlobPattern ('\\':c:rest) = 
    if (c == globSeparator)
    then GlobBadPattern $ "illegal escaped separator character at '" ++ (c:rest) ++ "'"
    else GlobMatch [c] (parseGlobPattern rest)
parseGlobPattern s = 
    let (exact,rest) = break (`elem` (globSeparator:"*?[\\")) s
    in if ([globSeparator] `isPrefixOf` exact)
       then GlobBadPattern $ "illegal separator character at '" ++ exact ++ "'"
       else GlobMatch exact (parseGlobPattern rest)

-- Parse character class specifications
parseCharClasses :: String -> ([CharClass],String)
parseCharClasses "" = ([BadCharClass "no terminating ']'"],"")
parseCharClasses (x:s) = 
    let (xs,rest) = break (== ']') s
    in if (null rest)
       then ([BadCharClass "no terminating ']'"],"")
       else (parseCC (x:xs), tail rest)
  where parseCC "" = []
        parseCC (c1:'-':c2:rest) = (CharRange c1 c2):(parseCC rest)
        parseCC ('-':rest) = (CharList ['-']) `combineCC` (parseCC rest)
        parseCC [c] = [CharList [c]]
        parseCC s = let (first,rest) = break (== '-') s
                    in (CharList (init first)) `combineCC` (parseCC ((last first):rest))
        combineCC (CharList []) xs = xs
        combineCC (CharList xs) ((CharList ys):cs) = (CharList (xs ++ ys)):cs
        combineCC x xs = x:xs

-- Test if a pattern contains GlobBadPattern
getGlobErr :: GlobPattern -> Maybe String
getGlobErr GlobEnd            = Nothing
getGlobErr (GlobMatch _ p)    = getGlobErr p
getGlobErr (GlobOneChar p)    = getGlobErr p
getGlobErr (GlobAnyChars p)   = getGlobErr p
getGlobErr (GlobOneOf _ p)    = getGlobErr p
getGlobErr (GlobNotOneOf _ p) = getGlobErr p
getGlobErr (GlobBadPattern s) = Just s

-- Test if a character class is a BadCharClass
getClassErr :: CharClass -> Maybe String
getClassErr (BadCharClass s) = Just s
getClassErr _                = Nothing

-- Test is a character is in a class
classContains :: CharClass -> Char -> Bool
classContains (CharRange lo hi) c = (c >= lo) && (c <= hi)
classContains (CharList cs) c     = c `elem` cs
classContains (BadCharClass _) _  = False

-- Match a string against a glob pattern
matchGlobPattern :: GlobPattern -> String -> Bool 
matchGlobPattern GlobEnd s = null s
matchGlobPattern (GlobMatch m p) s =
    if (m `isPrefixOf` s)
    then matchGlobPattern p (drop (length m) s)
    else False
matchGlobPattern (GlobOneChar p) [] = False
matchGlobPattern (GlobOneChar p) (_:s) = matchGlobPattern p s
matchGlobPattern (GlobAnyChars p) s =
    let (s',rest) = break ( == globSeparator) s
    in any (matchGlobPattern p) (map (++ rest) (tails s'))
matchGlobPattern (GlobOneOf xs p) [] = False
matchGlobPattern (GlobOneOf xs p) (c:s) = if (any (`classContains` c) xs)
                                          then matchGlobPattern p s
                                          else False
matchGlobPattern (GlobNotOneOf xs p) [] = False
matchGlobPattern (GlobNotOneOf xs p) (c:s) = if (any (`classContains` c) xs)
                                             then False
                                             else matchGlobPattern p s
matchGlobPattern (GlobBadPattern _) _ = False                                             

