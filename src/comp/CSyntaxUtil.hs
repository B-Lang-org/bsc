{-# LANGUAGE PatternGuards #-}
module CSyntaxUtil where

import CSyntax
import PreIds
import IntLit
import Position
import Id
import Type
import Data.Maybe

tMkTuple :: Position -> [CType] -> Type
tMkTuple pos [] = cTCon (setIdPosition pos idPrimUnit)
tMkTuple pos [t] = t
tMkTuple pos (t:ts) = tMkPair pos t (tMkTuple pos ts)

tMkPair :: Position -> Type -> Type -> Type
tMkPair pos t1 t2 = TAp (TAp (cTCon (setIdPosition pos idPrimPair)) t1) t2

tMkEitherChain :: Position -> [CType] -> Type
tMkEitherChain pos [] = error "Either with no options"
tMkEitherChain pos [t] = t
tMkEitherChain pos (t:ts) = tMkEither pos t (tMkEitherChain pos ts)

tMkEither :: Position -> Type -> Type -> Type
tMkEither pos t1 t2 = TAp (TAp (cTCon (setIdPosition pos idEither)) t1) t2

-- differs from tMkPair because the kind and other typeinfo is correct
mkPairType :: CType -> CType -> CType
mkPairType ft1 ft2 = TAp (TAp tPrimPair ft1) ft2

mkTuple :: Position -> [CExpr] -> CExpr
mkTuple pos [] = CStruct (setIdPosition pos idPrimUnit) []
mkTuple pos [e] = e
mkTuple pos (e:es) = CBinOp e (setIdPosition pos idComma) (mkTuple pos es)

pMkTuple :: Position -> [CPat] -> CPat
pMkTuple pos [] = CPstruct (setIdPosition pos idPrimUnit) []
pMkTuple pos [p] = p
pMkTuple pos (p:ps) = CPCon (setIdPosition pos idComma) [p, pMkTuple pos ps]

mkEitherChain :: Position -> Int -> Int -> CExpr -> CExpr
mkEitherChain pos 0 1 e = e
mkEitherChain pos 0 _ e = CCon idLeft [e]
mkEitherChain pos i n e
  | i < n = CCon idRight [mkEitherChain pos (i - 1) (n - 1) e]
  | otherwise = error $ "Index " ++ show i ++ " out of range for Either chain of size " ++ show n

pMkEitherChain :: Position -> Int -> Int -> CPat -> CPat
pMkEitherChain pos 0 1 e = e
pMkEitherChain pos 0 _ e = CPCon idLeft [e]
pMkEitherChain pos i n e
  | i < n = CPCon idRight [pMkEitherChain pos (i - 1) (n - 1) e]
  | otherwise = error $ "Index " ++ show i ++ " out of range for Either chain of size " ++ show n

mkMaybe :: (Maybe CExpr) -> CExpr
mkMaybe Nothing = CCon idInvalid []
mkMaybe (Just e) = CCon idValid [e]

num_to_cliteral_at :: Integral n => Position -> n -> CLiteral
num_to_cliteral_at pos num = CLiteral pos $ LInt $ ilDec (toInteger num)

numLiteralAt :: Integral n => Position -> n -> CExpr
numLiteralAt pos num = CLit $ num_to_cliteral_at pos num

-- create a string literal at a given position
stringLiteralAt :: Position -> String -> CExpr
stringLiteralAt pos s = CLit $ CLiteral pos $ LString s

typeLiteral :: CType -> CExpr
typeLiteral t = cVApply idTypeOf [CHasType anyExpr (CQType [] t)]

posLiteral :: Position -> CExpr
posLiteral pos = CLit $ CLiteral pos LPosition

noRead :: CExpr -> CExpr
noRead e = (CApply (CVar idAsIfc) [e])

data SizeGuess = Guess CType
               | NoGuess
               | BadSize Integer Position
               | BadIndex Integer Position
-- A heuristic to guess the size of an e[h:l] expression.
guessBitSize :: CExpr -> CExpr -> SizeGuess
-- XXX This relies on Eq of CExpr to ignore positions
guessBitSize h l | h == l = Guess (TAp tBit (tOfSize 1 (getPosition h)))
guessBitSize (CLit (CLiteral pos (LInt hi))) (CLit (CLiteral pos' (LInt lo)))
    | ilValue hi < 0 = BadIndex (ilValue hi) pos
    | ilValue lo < 0 = BadIndex (ilValue lo) pos'
    | ilValue hi >= ilValue lo = Guess (TAp tBit (tOfSize (ilValue hi - ilValue lo + 1) pos))
    | otherwise = BadSize (ilValue hi - ilValue lo + 1) pos
guessBitSize (CBinOp x plus (CLit (CLiteral pos (LInt hi)))) x'
    | plus == idPlus, x == x' =
        if ilValue hi >= 0 then
            Guess (TAp tBit (tOfSize (ilValue hi + 1) pos))
        else BadSize (ilValue hi + 1) pos
guessBitSize (CBinOp x  plus  (CLit (CLiteral pos (LInt hi))))
             (CBinOp x' plus' (CLit (CLiteral   _ (LInt lo))))
    | plus == idPlus, x == x', plus' == idPlus =
        if ilValue hi >= ilValue lo then
            Guess (TAp tBit (tOfSize (ilValue hi - ilValue lo + 1) pos))
        else BadSize (ilValue hi - ilValue lo + 1) pos
guessBitSize x (CBinOp x' minus (CLit (CLiteral pos (LInt hi))))
    | x == x', minus == idMinus =
        if ilValue hi >= 0 then
            Guess (TAp tBit (tOfSize (ilValue hi + 1) pos))
        else BadSize (ilValue hi + 1) pos
guessBitSize (CBinOp x  minus  (CLit (CLiteral pos (LInt lo))))
             (CBinOp x' minus' (CLit (CLiteral   _ (LInt hi))))
    | minus == idMinus, x == x', minus' == idMinus =
       if ilValue hi >= ilValue lo then
           Guess (TAp tBit (tOfSize (ilValue hi - ilValue lo + 1) pos))
       else BadSize (ilValue hi - ilValue lo + 1) pos
guessBitSize (CBinOp x  plus  (CLit (CLiteral pos (LInt hi))))
             (CBinOp x' minus (CLit (CLiteral   _ (LInt lo))))
    | plus == idPlus, x == x', minus == idMinus =
        if (ilValue hi + ilValue lo) >= 0 then
            Guess (TAp tBit (tOfSize (ilValue hi + ilValue lo + 1) pos))
        else BadSize (ilValue hi + ilValue lo + 1) pos
guessBitSize _ _ = NoGuess

mkNameExprAt :: Position -> Id -> CExpr
mkNameExprAt pos i = (CApply (CVar (idPrimGetNameAt pos)) [CVar i])

mkNameExpr :: Id -> CExpr
mkNameExpr i = mkNameExprAt (getPosition i) i

applyToCExprIds :: (Id -> Id) -> CExpr -> CExpr
applyToCExprIds f (CApply x y) =  (CApply (applyToCExprIds f x) (map (applyToCExprIds f) y))
applyToCExprIds f (CVar id) = (CVar (f id))
applyToCExprIds f c = c

-- isEnum: checks if a data declaration creates an enumeration
-- (based on the original constructors):
-- if the tags have no arguments, it's an enum type
isEnum :: COSummands -> Bool
isEnum = all (null . cos_arg_types)

-- does a data declaration have contiguous tags?
contiguousTags :: [CInternalSummand] -> Bool
contiguousTags = is_contiguous_seq . (map cis_tag_encoding)

-- is_contiguous_seq: checks if a numeric sequence [0..] is contiguous
is_contiguous_seq :: (Eq n, Num n) => [n] -> Bool
is_contiguous_seq [0] = True
is_contiguous_seq (0:1:rest) =
    let check_diff Nothing _ = Nothing
        check_diff (Just current) next | next - current == 1 = Just next
                                       | otherwise = Nothing
    in  isJust (foldl check_diff (Just 1) rest)
is_contiguous_seq _ = False
