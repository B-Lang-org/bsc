-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module Sort(sortLe) where

sortLe :: (a -> a -> Bool) -> [a] -> [a]
sortLe le l = tmsort le l

--sort :: (Ord a) => [a] -> [a]
--sort l = tmsort (<=) l

tmsort :: (a -> a -> Bool) -> [a] -> [a]
tmsort _ [] = []
tmsort _ [x] = [x]                -- just for speed
tmsort le (x:xs) = msort le (upSeq le xs [x])

upSeq :: (a -> a -> Bool) -> [a] -> [a] -> [[a]]
upSeq _  [] xs = [reverse xs]
upSeq le (y:ys) xxs@(x:xs) =
        if le x y then
            upSeq le ys (y:xxs)
        else
            reverse xxs : upSeq le ys [y]
upSeq _ _ [] = error ("Sort.hs :: upSeq unexpected pattern" )

msort :: (a -> a -> Bool) -> [[a]] -> [a]
msort _ [xs] = xs
msort le xss = msort le (mergePairs le xss)

mergePairs :: (a -> a -> Bool) -> [[a]] -> [[a]]
mergePairs le (xs:ys:xss) = merge le xs ys : mergePairs le xss
mergePairs _  xss = xss

merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge le xxs@(x:xs) yys@(y:ys) =
        if le x y then
            x:merge le xs yys
        else
            y:merge le xxs ys
merge _  []         yys = yys
merge _  xxs        []  = xxs
