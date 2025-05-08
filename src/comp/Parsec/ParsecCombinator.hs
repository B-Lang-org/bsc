-----------------------------------------------------------------------------
-- |
-- Module      :  ParsecCombinator
-- Copyright   :  (c) Daan Leijen 1999-2001
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  daan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- Commonly used generic combinators
--
-----------------------------------------------------------------------------

module ParsecCombinator
                        ( choice
                        , count
                        , between
                        , option, optional
                        , skipMany1
                        , many1
                        , sepBy, sepBy1
                        , endBy, endBy1
                        , sepEndBy, sepEndBy1
                        , chainl, chainl1
                        , chainr, chainr1
                        , eof, notFollowedBy

                        -- tricky combinators
                        , manyTill, lookAhead, anyToken
                        ) where

import Control.Monad
import ParsecPrim


----------------------------------------------------------------
--
----------------------------------------------------------------
choice :: [GenParser tok st a] -> GenParser tok st a
choice ps           = foldr (<|>) mzero ps

option :: a -> GenParser tok st a -> GenParser tok st a
option x p          = p <|> return x

optional :: GenParser tok st a -> GenParser tok st ()
optional p          = do{ _ <- p; return ()} <|> return ()

between :: GenParser tok st open -> GenParser tok st close
            -> GenParser tok st a -> GenParser tok st a
between open close p
                    = do{ _ <- open; x <- p; _ <- close; return x }


skipMany1 :: GenParser tok st a -> GenParser tok st ()
skipMany1 p         = do{ _ <- p; skipMany p }
{-
skipMany p          = scan
                    where
                      scan  = do{ p; scan } <|> return ()
-}

many1 :: GenParser tok st a -> GenParser tok st [a]
many1 p             = do{ x <- p; xs <- many p; return (x:xs) }
{-
many p              = scan id
                    where
                      scan f    = do{ x <- p
                                    ; scan (\tail -> f (x:tail))
                                    }
                                <|> return (f [])
-}

sepBy1,sepBy :: GenParser tok st a -> GenParser tok st sep -> GenParser tok st [a]
sepBy p sep         = sepBy1 p sep <|> return []
sepBy1 p sep        = do{ x <- p
                        ; xs <- many (sep >> p)
                        ; return (x:xs)
                        }

sepEndBy1, sepEndBy :: GenParser tok st a -> GenParser tok st sep -> GenParser tok st [a]
sepEndBy1 p sep     = do{ x <- p
                        ; do{ _ <- sep
                            ; xs <- sepEndBy p sep
                            ; return (x:xs)
                            }
                          <|> return [x]
                        }

sepEndBy p sep      = sepEndBy1 p sep <|> return []


endBy1,endBy :: GenParser tok st a -> GenParser tok st sep -> GenParser tok st [a]
endBy1 p sep        = many1 (do{ x <- p; _ <- sep; return x })
endBy p sep         = many (do{ x <- p; _ <- sep; return x })

count :: Int -> GenParser tok st a -> GenParser tok st [a]
count n p           | n <= 0    = return []
                    | otherwise = sequence (replicate n p)


chainr,chainl :: GenParser tok st a -> GenParser tok st (a -> a -> a) -> a -> GenParser tok st a
chainr p op x       = chainr1 p op <|> return x
chainl p op x       = chainl1 p op <|> return x

chainr1,chainl1 :: GenParser tok st a -> GenParser tok st (a -> a -> a) -> GenParser tok st a
chainl1 p op        = do{ x <- p; rest x }
                    where
                      rest x    = do{ f <- op
                                    ; y <- p
                                    ; rest (f x y)
                                    }
                                <|> return x

chainr1 p op        = scan
                    where
                      scan      = do{ x <- p; rest x }

                      rest x    = do{ f <- op
                                    ; y <- scan
                                    ; return (f x y)
                                    }
                                <|> return x

-----------------------------------------------------------
-- Tricky combinators
-----------------------------------------------------------
anyToken :: (tok -> String) -> GenParser tok st tok
anyToken show = tokenPrim show (\pos tok toks -> pos) Just

eof :: (tok -> String) -> GenParser tok st ()
eof show = notFollowedBy show (anyToken show) <?> "end of input"

notFollowedBy :: (tok -> String) -> GenParser tok st tok -> GenParser tok st ()
notFollowedBy show p = try (do{ c <- p; unexpected (show c) }
                            <|> return ())

manyTill :: GenParser tok st a -> GenParser tok st end -> GenParser tok st [a]
manyTill p end      = scan
                    where
                      scan  = do{ _ <- end; return [] }
                            <|>
                              do{ x <- p; xs <- scan; return (x:xs) }


lookAhead :: GenParser tok st a -> GenParser tok st a
lookAhead p         = do{ state <- getParserState
                        ; x <- p
                        ; _ <- setParserState state
                        ; return x
                        }
