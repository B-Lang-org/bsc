{-# LANGUAGE CPP #-}
module PPrint(PPrint(..), PDetail(..), module Pretty,
        ppReadable, ppReadableIndent, ppAll, ppDebug, ppString, pp80,
        pparen, sepList, catList, vcatList, ppr, ppDoc,
        maxPrec, vsep, wrap, commaSep, encloseSep,
        tracePPS,
        ShortBool, toTF
        ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Pretty
import Util(itos)
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S

-- wrap :: lines in -> lines out with long lines broken up
wrap :: [String] -> [String]
wrap [] = []
wrap (s:rest) | length s > 75 = (take 75 s):(wrap ((drop 75 s):rest))
wrap (s:rest) = s:(wrap rest)


data PDetail = PDReadable | PDAll | PDDebug | PDMark | PDInfo | PDNoqual deriving (Eq, Ord, Show)

class PPrint a where
    pPrint :: PDetail -> Int -> a -> Doc
--    pPrint _ _ x = text ("***"++show x++"***")

-- the second argument to pretty ("ribbons per line") is the maximum number
-- of non-indent characters on a line (according to Wadler's "prettier print"
-- paper).  So this is irrelevant to Verilog.  So use the same number as
-- characters per line.  And add a margin by dropping 80 to, say, 78.
pp80 :: (PPrint a) => a -> String
pp80 = pretty 78 78 . pPrint PDReadable 0

ppReadable :: (PPrint a) => a -> String
ppReadable = ppr PDReadable

ppReadableIndent :: (PPrint a) => Int -> a -> String
ppReadableIndent i = pprIndent i PDReadable

ppAll :: (PPrint a) => a -> String
ppAll = ppr PDAll

ppDebug :: (PPrint a) => a -> String
ppDebug = ppr PDDebug

lineWidth, linePref :: Int
lineWidth = 120
linePref = 100

ppString :: PPrint a => a -> String
ppString = init . pretty 100000 100000 . pPrint PDReadable 0

ppr :: PPrint a => PDetail -> a -> String
ppr d = pretty lineWidth linePref . pPrint d 0

pprIndent :: PPrint a => Int -> PDetail -> a -> String
pprIndent i d = pretty lineWidth linePref . nest i . pPrint d 0

ppDoc :: Doc -> String
ppDoc d = pretty lineWidth linePref d

-- trace, pretty printing the object with a prefix
-- e.g.  tracePP "Test1" x
tracePPS :: (PPrint a) => String -> a -> a
tracePPS s x = trace msg x
    where msg = s ++ " " ++ ppString x


instance PPrint Int where
    pPrint _ _ x = text (itos x)

instance PPrint Integer where
    pPrint _ _ x = text (itos x)

instance PPrint Bool where
    pPrint _ _ x = text (show x)

instance PPrint Char where
    pPrint _ _ x = text (show x)

-- instance PPrint String where
--     pPrint _ _ x = doubleQuotes $ text x

instance PPrint Double where
    pPrint _ _ x = text (show x)

instance PPrint Float where
    pPrint _ _ x = text (show x)

instance (PPrint a, PPrint b) => PPrint (a, b) where
    pPrint d _ (x, y) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y] <> text ")"

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
    pPrint d _ (x, y, z) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y <> text ",", pPrint d 0 z] <> text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d) => PPrint (a, b, c, d) where
    pPrint d _ (x, y, z, w) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y <> text ",", pPrint d 0 z <> text ",", pPrint d 0 w] <> text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e) => PPrint (a, b, c, d, e) where
    pPrint d _ (x, y, z, w, v) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y <> text ",", pPrint d 0 z <> text ",", pPrint d 0 w <> text ",", pPrint d 0 v] <> text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e, PPrint f) => PPrint (a, b, c, d, e, f) where
    pPrint d _ (x, y, z, w, v, u) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y <> text ",", pPrint d 0 z <> text ",", pPrint d 0 w <> text ",", pPrint d 0 v <> text ",", pPrint d 0 u] <> text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e, PPrint f, PPrint g) => PPrint (a, b, c, d, e, f, g) where
    pPrint d _ (x, y, z, w, v, u, t) = text "(" <> sep [pPrint d 0 x <> text ",", pPrint d 0 y <> text ",", pPrint d 0 z <> text ",", pPrint d 0 w <> text ",", pPrint d 0 v <> text ",", pPrint d 0 u <> text ",", pPrint d 0 t] <> text ")"

instance (PPrint a) => PPrint [a] where
    pPrint d _ xs = let xs' = map (pPrint d 0) xs
                    in  text "[" <> commaSep xs' <> text "]"

instance (PPrint a, PPrint b) => PPrint (Either a b) where
    pPrint d p (Left x) = pparen (p>9) (text"(Left" <+> pPrint d 10 x <> text")")
    pPrint d p (Right x) = pparen (p>9) (text"(Right" <+> pPrint d 10 x <> text")")

instance (PPrint a) => PPrint (Maybe a) where
    pPrint _ _ Nothing = text"Nothing"
    pPrint d p (Just x) = pparen (p>9) (text"Just (" <> pPrint d 10 x <> text")")

instance PPrint () where
    pPrint _ _ () = text "()"

instance (PPrint a, PPrint b) => PPrint (M.Map a b) where
    pPrint d i m = vsep [pPrint d 0 k <+> text "->" <+> pPrint d 0 v
                         | (k, v) <- M.toList m]

instance (PPrint a, Ord a) => PPrint (S.Set a) where
    pPrint d i s = pPrint d i (S.toList s)


pparen :: Bool -> Doc -> Doc
pparen False x = x
pparen True  x = text"(" <> x <> text")"

sepList :: [Doc] -> Doc -> Doc
sepList [] _ = empty
sepList xs s = sep (map (\x->x <> s) (init xs) ++ [last xs])

catList :: [Doc] -> Doc -> Doc
catList [] _ = empty
catList xs s = cat (map (\x->x <> s) (init xs) ++ [last xs])

-- unlike sepList, this will force one per line
vcatList :: [Doc] -> Doc -> Doc
vcatList [] _ = empty
vcatList xs s = vcat (map (\x->x <> s) (init xs) ++ [last xs])

vsep :: [Doc] -> Doc
vsep = foldr ($+$) empty

-- print a list with entries separated by commas, either
-- horizontally or vertically, depending on what fits
commaSep :: [Doc] -> Doc
commaSep [] = empty
commaSep ds = sep ([x <> comma | x <- init ds] ++ [last ds])

maxPrec :: Int
maxPrec = 20

encloseSep :: Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSep left right punc ds =
    case ds of
      []  -> left <+> right
      [d] -> left <+> d <+> right
      _   -> let ps = zipWith (<+>) (left : repeat punc) ds
             in  sep (ps ++ [right])

-------------------
-- a simple type to allowing display of True/False as "T"/"F"
-- typical usage  trace (ppReadable (toTF x) ) (x)
data ShortBool = FALSE | TRUE
                     deriving (Show)

instance PPrint ShortBool where
  pPrint _ _ TRUE = text "T"
  pPrint _ _ FALSE = text "F"

toTF :: Bool -> ShortBool
toTF True = TRUE
toTF _    = FALSE
