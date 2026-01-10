{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
module Position where

import Data.List(partition)
import qualified Data.Generics as Generic

import Eval(NFData(..))
import PPrint
import PVPrint
import FStringCompat
import PreStrings(fsEmpty)
import FileNameUtil(getRelativeFilePath)

data Position = Position {
    pos_file :: !FString,
    pos_line :: !Int,
    pos_column :: !Int,
    pos_is_stdlib :: !Bool
} deriving (Generic.Data, Generic.Typeable)

mkPosition :: FString -> Int -> Int -> Position
mkPosition f l c = Position f l c False

mkPositionFull :: FString -> Int -> Int -> Bool -> Position
mkPositionFull f l c is_stdlib = Position f l c is_stdlib

instance Eq Position where
  (Position f1 l1 c1 _) == (Position f2 l2 c2 _) = (f1, l1, c1) == (f2, l2, c2)

instance Ord Position where
  compare (Position f1 l1 c1 _) (Position f2 l2 c2 _) = compare (f1, l1, c1) (f2, l2, c2)

class HasPosition a where
    getPosition :: a -> Position

instance Show Position where
    show p = prPosition p

instance NFData Position where
    rnf (Position _ _ _ _) = ()

prPosition :: Position -> String
prPosition (Position fs l c pred) =
    let f = getFString fs
        f' = getRelativeFilePath f
    in
    if l==(-2) && c<0 && f=="" then "Command line" else
    if l<0 && c<0 && f=="" then "Unknown position" else
    let lc = if l<0 then "" else "line " ++ show3 l ++ (if c < 0 then "" else ", column "++show3 c)
        show3 = show --until ((>=3) . length) (' ':) . show
    in        case f of
            "" -> lc
            _ -> show f' ++ (if null lc then "" else ", "++lc)

prPositionConcise :: Position -> String
prPositionConcise (Position fs l c pred) =
    let f = getFString fs
        f' = getRelativeFilePath f
    in
    if l==(-2) && c<0 && f=="" then "Command line" else
    if l<0 && c<0 && f=="" then "Unknown position" else
    let lc = if l<0 then "" else ":" ++ show3 l ++ (if c < 0 then "" else ":"++show3 c)
        show3 = show --until ((>=3) . length) (' ':) . show
    in        case f of
            "" -> lc
            _ -> f' ++ lc

instance HasPosition Position where
    getPosition p = p

-- #############################################################################
-- #
-- #############################################################################


firstPos :: [Position] -> Position
firstPos ps = case filter (/= noPosition) ps of
              []  -> noPosition
              [p] -> p
              psf -> firstPos2 psf

firstPos2 :: [Position] -> Position
firstPos2 [] = noPosition
firstPos2 ps = case filter isUsefulPosition ps of
              []  -> -- trace("none " ++ (show (length ps)) ++ "\n") $
                     head ps
              [p] -> p
              filtered -> -- trace("first " ++ (show (length filtered)) ++ "\n") $
                          head filtered

-- #############################################################################
-- #
-- #############################################################################

isUsefulPosition :: Position -> Bool
isUsefulPosition pos@(Position fs line column pred) =
    (not pred) -- && (not ((getFString fs) == "INTERNAL"))


-- if no useful position is found in the list, returns first non-empty pos.
-- takes a default if no non-empty position is found
getMostUsefulPosition :: [Position] -> Position -> Position
getMostUsefulPosition [] dflt = dflt
getMostUsefulPosition xs dflt =
    let nonempty_xs = filter (/= noPosition) xs
        (useful,nonuseful) = partition isUsefulPosition nonempty_xs
    in  case (useful) of
            (p:_) -> p
            [] -> case (nonuseful) of
                      (p:_) -> p
                      _ -> dflt

-- #############################################################################
-- #
-- #############################################################################

isPreludePosition :: Position -> Bool
isPreludePosition = pos_is_stdlib

-- #############################################################################
-- #
-- #############################################################################

cmdPosition :: Position
cmdPosition = mkPosition fsEmpty (-2) (-1)

noPosition :: Position
noPosition = mkPosition fsEmpty (-1) (-1)

remPositionFile :: Position -> Position
remPositionFile (Position _ l c _) = mkPosition fsEmpty l c

filePosition :: FString -> Position
filePosition f = mkPosition f (-1) (-1)


initialPosition :: String -> Position
initialPosition f = mkPosition (mkFString f) 1 1


newPosition :: String -> Int -> Int -> Position
newPosition f l c = mkPosition (mkFString f) l c

newLinePosition :: String -> Int -> Position
newLinePosition f l = mkPosition (mkFString f) l 1


updatePosChar :: Position -> Char -> Position
updatePosChar specialPos@(Position _ _ (-1) _) _ = specialPos
updatePosChar (Position file line column pred) '\n' = Position file (line+1) 1 pred
updatePosChar (Position file line column pred) '\t' = Position file line (column + 8 - ((column - 1) `mod` 8)) pred
updatePosChar (Position file line column pred) _ = Position file line (column + 1) pred

isFirstColumn :: Position -> Bool
isFirstColumn pos = (getPositionColumn pos) == 1

-- backspace one column (only works for same-line when column > 1)
updatePosBackspace :: Position -> Position
updatePosBackspace pos@(Position file line column pred)
    | column > 1 = Position file line (column - 1) pred
    | otherwise = pos


updatePosLineCol :: Position -> Int -> Int -> Position
updatePosLineCol (Position f _ _ pred) newl newc =
        Position f newl newc pred

updatePosFile :: Position -> FString -> Position
updatePosFile (Position _ l c pred) newf =
        Position newf l c pred

updatePosFileLineCol :: Position -> FString -> Int -> Int -> Position
updatePosFileLineCol (Position _ _ _ pred) newf newl newc =
        Position newf newl newc pred

updatePosString :: Position -> String -> Position
updatePosString pos str = foldl updatePosChar pos str

updatePosStdlib :: Position -> Bool -> Position
updatePosStdlib pos is_stdlib = pos { pos_is_stdlib = is_stdlib }

-- returns a pair of positions (pos1, pos2) where
--   pos1 points at the last character of the input string
--   pos2 points at the first character beyond the input string
posAtEndAndAfterString :: Position -> String -> (Position, Position)
posAtEndAndAfterString pos "" = (updatePosBackspace pos, pos)
posAtEndAndAfterString pos [char] = (pos, updatePosChar pos char)
posAtEndAndAfterString pos (char:chars) =
    posAtEndAndAfterString (updatePosChar pos char) chars


getPositionColumn :: Position -> Int
getPositionColumn (Position _ _ c _) = c

getPositionLine :: Position -> Int
getPositionLine (Position _ l _ _) = l


getPositionFile :: Position -> String
getPositionFile (Position fs _ _ _) = getFString fs

instance PPrint Position where
    pPrint _ _ p = text (prPosition p)

instance PVPrint Position where
    pvPrint _ _ p = text (prPosition p)

bestPosition :: Position -> Position -> Position
bestPosition p1 p2 = if p1 == noPosition then p2 else p1

instance (HasPosition a) => HasPosition (Maybe a) where
    getPosition (Just x) = getPosition x
    getPosition Nothing = noPosition

instance (HasPosition a, HasPosition b) => HasPosition (Either a b) where
    getPosition (Right x) = getPosition x
    getPosition (Left x) = getPosition x

instance (HasPosition a) => HasPosition [a] where
    getPosition [] = noPosition
    getPosition (x:xs) = getPosition x `bestPosition` getPosition xs

instance (HasPosition a, HasPosition b) => HasPosition (a, b) where
    getPosition (x, y) = getPosition x `bestPosition` getPosition y

instance (HasPosition a, HasPosition b, HasPosition c) => HasPosition (a, b, c) where
    getPosition (x, y, z) = getPosition x `bestPosition` getPosition y `bestPosition` getPosition z

instance (HasPosition a, HasPosition b, HasPosition c, HasPosition d) => HasPosition (a, b, c, d) where
    getPosition (x, y, z, w) = getPosition x `bestPosition` getPosition y `bestPosition` getPosition z `bestPosition` getPosition w

instance HasPosition String where
    getPosition x = noPosition
