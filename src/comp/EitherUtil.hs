module EitherUtil where
-- work around lefts, rights and partitionEithers not being in Data.Either for base 3

partitionEithers :: [Either a b] -> ([a],[b])
partitionEithers [] = ([],[])
partitionEithers (Left  a : rest) = (a:as, bs)
  where (as,bs) = partitionEithers rest
partitionEithers (Right b : rest) = (as, b:bs)
  where (as,bs) = partitionEithers rest

lefts :: [Either a b] -> [a]
lefts = fst . partitionEithers

rights :: [Either a b] -> [b]
rights = snd . partitionEithers
