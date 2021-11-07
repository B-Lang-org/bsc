{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ParsecPrim
-- Copyright   :  (c) Daan Leijen 1999-2001
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  daan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- The primitive parser combinators.
--
-----------------------------------------------------------------------------

module ParsecPrim
                   ( -- operators: label a parser, alternative
                     (<?>), (<|>)

                   -- basic types
                   , Parser, GenParser
                   , runParser, parse, parseFromFile, parseTest

                   -- primitive parsers:
                   -- instance Functor Parser     : fmap
                   -- instance Monad Parser       : return, >>=, fail
                   -- instance MonadPlus Parser   : mzero (pzero), mplus (<|>)
                   , token, tokens, tokenPrim, tokenPrimEx
                   , try, label, labels, unexpected, pzero

                   -- advanced error handling:
                   , failWithErr, failWithErrs
                   , unexpectedAt

                   -- primitive because of space behaviour
                   , many, skipMany

                   -- user state manipulation
                   , getState, setState, updateState

                   -- state manipulation
                   , getPosition, setPosition
                   , getInput, setInput
                   , getParserState, setParserState

                   -- IO/parser interaction
                   , ioToParser
                 ) where

import Prelude
import Data.List
import qualified Control.Applicative as App(Applicative(..), Alternative(..))
import Control.Monad
#if !defined(__GLASGOW_HASKELL__) || ((__GLASGOW_HASKELL__ >= 800) && (__GLASGOW_HASKELL__ < 808))
import Control.Monad.Fail(MonadFail(..))
#endif
import Error(EMsg, ErrMsg(..)) -- from BSC
import Position hiding(getPosition) -- from BSC

{-# INLINE parsecMap    #-}
{-# INLINE parsecReturn #-}
{-# INLINE parsecBind   #-}
{-# INLINE parsecZero   #-}
{-# INLINE parsecPlus   #-}
{-# INLINE token        #-}
{-# INLINE tokenPrim    #-}

-----------------------------------------------------------
-- Operators:
-- <?>  gives a name to a parser (which is used in error messages)
-- <|>  is the choice operator
-----------------------------------------------------------
infix  0 <?>
infixr 1 <|>

(<?>) :: GenParser tok st a -> String -> GenParser tok st a
p <?> msg           = label p msg

(<|>) :: GenParser tok st a -> GenParser tok st a -> GenParser tok st a
p1 <|> p2           = mplus p1 p2


-----------------------------------------------------------
-- User state combinators
-----------------------------------------------------------
getState :: GenParser tok st st
getState        = do{ state <- getParserState
                    ; return (stateUser state)
                    }

setState :: st -> GenParser tok st ()
setState st     = do{ _ <- updateParserState (\(State input pos _) -> State input pos st)
                    ; return ()
                    }

updateState :: (st -> st) -> GenParser tok st ()
updateState f   = do{ _ <- updateParserState (\(State input pos user) -> State input pos (f user))
                    ; return ()
                    }


-----------------------------------------------------------
-- Parser state combinators
-----------------------------------------------------------
getPosition :: GenParser tok st Position
getPosition         = do{ state <- getParserState; return (statePos state) }

getInput :: GenParser tok st [tok]
getInput            = do{ state <- getParserState; return (stateInput state) }


setPosition :: Position -> GenParser tok st ()
setPosition pos     = do{ _ <- updateParserState (\(State input _ user) -> State input pos user)
                        ; return ()
                        }

setInput :: [tok] -> GenParser tok st ()
setInput input      = do{ _ <- updateParserState (\(State _ pos user) -> State input pos user)
                        ; return ()
                        }

getParserState      :: GenParser tok st (State tok st)
getParserState      =  updateParserState id

setParserState      :: State tok st -> GenParser tok st (State tok st)
setParserState st   = updateParserState (const st)




-----------------------------------------------------------
-- Parser definition.
-- GenParser tok st a:
--  General parser for tokens of type "tok",
--  a user state "st" and a result type "a"
-----------------------------------------------------------
type Parser a           = GenParser Char () a

newtype GenParser tok st a = Parser (State tok st -> IO (Consumed (Reply tok st a)))

runP :: GenParser tok st a -> State tok st -> IO (Consumed (Reply tok st a))
runP (Parser p)            = p

data Consumed a         = Consumed a                --input is consumed
                        | Empty !a                  --no input is consumed

data Reply tok st a     = Ok !a !(State tok st) [EMsg]   --parsing succeeded with "a"
                        | Error !Bool [EMsg]          --parsing failed
                                                    --bool means deadliness:
                                                    -- when true, merging this
                                                    -- error with anything
                                                    -- gives this error

data State tok st       = State { stateInput :: [tok]
                                , statePos   :: !Position
                                , stateUser  :: !st
                                }


-----------------------------------------------------------
-- run a parser
-----------------------------------------------------------
parseFromFile :: Parser a -> FilePath -> IO (Either [EMsg] a)
parseFromFile p fname
    = do{ input <- readFile fname
        ; parse p fname input
        }

parseTest :: Show a => GenParser tok () a -> [tok] -> IO ()
parseTest p input
    = do reply <- runParser p () (initialPosition "") input
         case reply of
           Left err -> do{ putStr "parse error at "
                         ; print err
                         }
           Right x  -> print x


parse :: GenParser tok () a -> FilePath -> [tok] -> IO (Either [EMsg] a)
parse p name input
    = runParser p () (initialPosition name) input


runParser :: GenParser tok st a -> st -> Position -> [tok]
          -> IO (Either [EMsg] a)
runParser p st pos input
    = do reply <- runP p (State input pos st)
         case parserReply reply of
           Ok x _ _         -> return (Right x)
           Error deadly err -> return (Left err)

ioToParser :: IO a -> GenParser tok st a
ioToParser computation =
    Parser (\state -> do result <- computation
                         return (Empty (Ok result state [])))

parserReply :: Consumed a -> a
parserReply result = case result of
        Consumed reply -> reply
        Empty reply    -> reply


-----------------------------------------------------------
-- Functor: fmap
-----------------------------------------------------------
instance Functor (GenParser tok st) where
  fmap f p  = parsecMap f p

parsecMap :: (a -> b) -> GenParser tok st a -> GenParser tok st b
parsecMap f (Parser p)
    = Parser (\state ->
        do reply <- p state
           case reply of
              Consumed reply -> return $ Consumed (mapReply reply)
              Empty    reply -> return $ Empty    (mapReply reply))
    where
      mapReply reply
        = case reply of
            Ok x state err   -> let fx = f x
                                in seq fx (Ok fx state err)
            Error deadly err -> Error deadly err

-----------------------------------------------------------
-- Applicative
-----------------------------------------------------------

instance App.Applicative (GenParser tok st) where
  pure x = parsecReturn x
  (<*>) = ap

-----------------------------------------------------------
-- Alternative
-----------------------------------------------------------

instance App.Alternative (GenParser tok st) where
    (<|>) = mplus
    empty = mzero

-----------------------------------------------------------
-- Monad: return, sequence (>>=) and fail
-----------------------------------------------------------
instance Monad (GenParser tok st) where
  return     = pure
  p >>= f    = parsecBind p f
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 808)
  fail msg   = parsecFail msg
#endif

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 800)
instance MonadFail (GenParser tok st) where
  fail msg   = parsecFail msg
#endif

parsecReturn :: a -> GenParser tok st a
parsecReturn x
  = Parser (\state -> return $ Empty (Ok x state []))

parsecBind :: GenParser tok st a -> (a -> GenParser tok st b) -> GenParser tok st b
parsecBind (Parser p) f
    = Parser (\state ->
        do reply <- p state
           case reply of
              Consumed reply1
                -> case (reply1) of
                     Ok x state1 err1 ->
                         do reply' <- runP (f x) state1
                            case reply' of
                                Empty reply2    ->
                                   return (Consumed
                                           (mergeErrorReply err1 reply2))
                                Consumed reply2 -> return (Consumed reply2)
                     Error evil err1  -> return (Consumed (Error evil err1))
              Empty reply1
                -> case (reply1) of
                     Ok x state1 err1 ->
                         do reply' <- runP (f x) state1
                            case reply' of
                              Empty reply2 ->
                                  return (Empty (mergeErrorReply err1 reply2))
                              other        -> return other
                     Error evil err1  -> return (Empty (Error evil err1)))

mergeErrorReply :: [EMsg] -> Reply tok st a -> Reply tok st a
mergeErrorReply err1 reply
  = case reply of
      Ok x state err2 -> Ok x state (mergeErrors err1 err2)
      Error True err2 -> Error True err2 -- deadly error
      Error False err2 -> Error False (mergeErrors err1 err2)


-- combine error messages
mergeErrors :: [EMsg] -> [EMsg] -> [EMsg]
mergeErrors = mergeErrors' (True, True)

-- bools are (leftrecurse, rightrecurse)
mergeErrors' :: (Bool, Bool) -> [EMsg] -> [EMsg] -> [EMsg]
mergeErrors' _ err1 []   = err1
mergeErrors' _ []   err2 = err2
mergeErrors' _ [e1] [e2] = mergeError e1 e2
mergeErrors' (lrec, True) errs errs' =
    foldr (mergeErrors' (lrec, False)) errs' [[e] | e <- sortBy cmpEMsg errs]
mergeErrors' (True, rrec) errs errs' =
    foldl (mergeErrors' (False, rrec)) errs [[e] | e <- sortBy cmpEMsg errs]
mergeErrors' _ errs errs' = sortBy cmpEMsg (errs ++ errs')

cmpEMsg :: EMsg -> EMsg -> Ordering
cmpEMsg (pos1, _) (pos2, _) = compare pos1 pos2

-- combine error messages
mergeError :: EMsg -> EMsg -> [EMsg]
mergeError (pos, ESyntax unexp exps) (pos', ESyntax unexp' exps')
    | unexp == unexp' && pos == pos' = [errSyntax pos unexp (exps ++ exps')]
mergeError err1 err2 = [err1, err2]


-- failures
parsecFail :: String -> GenParser tok st a
parsecFail msg
  = Parser (\state ->
            return (Empty (Error False [(statePos state, EGeneric msg)])))


failWithErr :: EMsg -> GenParser tok st a
failWithErr err
    = Parser (\state -> return (Empty (Error True [err])))

failWithErrs :: [EMsg] -> GenParser tok st a
failWithErrs errs
    = Parser (\state -> return (Empty (Error True errs)))

-----------------------------------------------------------
-- MonadPlus: alternative (mplus) and mzero
-----------------------------------------------------------
instance MonadPlus (GenParser tok st) where
  mzero         = parsecZero
  mplus p1 p2   = parsecPlus p1 p2


pzero :: GenParser tok st a
pzero = parsecZero

parsecZero :: GenParser tok st a
parsecZero
    = Parser (\state -> return (Empty (Error False [])))

parsecPlus :: GenParser tok st a -> GenParser tok st a -> GenParser tok st a
parsecPlus (Parser p1) (Parser p2)
    = Parser (\state ->
              do p1reply <- p1 state
                 case p1reply of
                   Empty (Error True err) ->
                     do p2reply <- p2 state
                        case p2reply of
                          Empty reply -> return (Empty (Error True err))
                          consumed    -> return consumed
                   Empty (Error False err) ->
                     do p2reply <- p2 state
                        case p2reply of
                          Empty reply ->
                            return (Empty (mergeErrorReply err reply))
                          consumed    -> return consumed
                   other             -> return other
      )


{-
-- variant that favors a consumed reply over an empty one, even it is not the first alternative.
          empty@(Empty reply) -> case reply of
                                   Error err ->
                                     case (p2 state) of
                                       Empty reply -> Empty (mergeErrorReply err reply)
                                       consumed    -> consumed
                                   ok ->
                                     case (p2 state) of
                                       Empty reply -> empty
                                       consumed    -> consumed
          consumed  -> consumed
-}


-----------------------------------------------------------
-- Primitive Parsers:
--  try, token(Prim), label, unexpected and updateState
-----------------------------------------------------------
try :: GenParser tok st a -> GenParser tok st a
try (Parser p)
    = Parser (\state@(State input pos user) ->
        do reply <- p state
           case reply of
              Consumed (Error deadly err)  ->
                  -- used to set position to pos (elf)
                  return (Empty (Error deadly err))
              Consumed ok           -> return (Consumed ok)    -- was: Empty ok
              empty                 -> return empty)

token :: (tok -> String) -> (tok -> Position) -> (tok -> Maybe a) -> GenParser tok st a
token show tokpos test
  = tokenPrim show nextpos test
  where
    nextpos _ _   (tok:toks)  = tokpos tok
    nextpos _ tok []          = tokpos tok

tokenPrim :: (tok -> String) -> (Position -> tok -> [tok] -> Position) -> (tok -> Maybe a) -> GenParser tok st a
tokenPrim show nextpos test
    = tokenPrimEx show nextpos Nothing test

-- | The most primitive token recogniser. The expression @tokenPrimEx show nextpos mbnextstate test@,
-- recognises tokens when @test@ returns @Just x@ (and returns the value @x@). Tokens are shown in
-- error messages using @show@. The position is calculated using @nextpos@, and finally, @mbnextstate@,
-- can hold a function that updates the user state on every token recognised (nice to count tokens :-).
-- The function is packed into a 'Maybe' type for performance reasons.
tokenPrimEx :: (tok -> String) ->
               (Position -> tok -> [tok] -> Position) ->
               Maybe (Position -> tok -> [tok] -> st -> st) ->
               (tok -> Maybe a) ->
               GenParser tok st a
tokenPrimEx show nextpos mbNextState test
    = case mbNextState of
        Nothing
          -> Parser (\state@(State input pos user) ->
              case input of
                (c:cs) -> case test c of
                            Just x  -> let newpos   = nextpos pos c cs
                                           newstate = State cs newpos user
                                       in seq newpos $ seq newstate $
                                          return (Consumed (Ok x newstate []))
                            Nothing ->
                               return (Empty (Error False
                                              [errSyntax pos (show c) []]))
                []     -> return (Empty (Error False [errSyntaxEof pos []]))
             )
        Just nextState
          -> Parser (\state@(State input pos user) ->
              case input of
                (c:cs) -> case test c of
                            Just x  -> let newpos   = nextpos pos c cs
                                           newuser  = nextState pos c cs user
                                           newstate = State cs newpos newuser
                                       in seq newpos $ seq newstate $
                                          return (Consumed (Ok x newstate []))
                            Nothing ->
                                return (Empty (Error False
                                               [errSyntax pos (show c) []]))
                []     -> return (Empty (Error False [errSyntaxEof pos []])))

label :: GenParser tok st a -> String -> GenParser tok st a
label p msg
  = labels p [msg]

labels :: GenParser tok st a -> [String] -> GenParser tok st a
labels (Parser p) msgs
    = Parser (\state ->
        do p_reply <- p state
           case p_reply of
              Empty reply -> return $ Empty $
                case (reply) of
                  Error True errs  -> Error True errs
                  Error False errs -> Error False (setExpectErrors errs msgs)
                  Ok x state1 []   -> reply
                  Ok x state1 errs -> Ok x state1 (setExpectErrors errs msgs)
              other       -> return other)

updateParserState :: (State tok st -> State tok st)
                  -> GenParser tok st (State tok st)
updateParserState f
    = Parser (\state -> let newstate = f state
                        in return (Empty (Ok state newstate [])))


unexpected :: String -> GenParser tok st a
unexpected msg
    = Parser (\state -> return (Empty (Error False
                                       [errSyntax (statePos state) msg []])))

unexpectedAt :: Position -> String -> GenParser tok st a
unexpectedAt pos msg
    = Parser (\state -> return (Empty (Error False [errSyntax pos msg []])))


setExpectErrors :: [EMsg] -> [String] -> [EMsg]
setExpectErrors [] _ = []
setExpectErrors errs [] = errs
setExpectErrors errs msgs | all null msgs = errs
setExpectErrors errs msgs = [setExpectError err msgs | err <- errs]

setExpectError :: EMsg -> [String] -> EMsg
setExpectError err@(pos, ESyntax unexp _) msgs =
    errSyntax pos unexp [msg | msg <- msgs, not (null msg)]
setExpectError (pos, _) msgs =
    errSyntax pos "???" [msg | msg <- msgs, not (null msg)]

-----------------------------------------------------------
-- Parsers unfolded for space:
-- if many and skipMany are not defined as primitives,
-- they will overflow the stack on large inputs
-----------------------------------------------------------
many :: GenParser tok st a -> GenParser tok st [a]
many p
  = do{ xs <- manyAccum (:) p
      ; return (reverse xs)
      }

skipMany :: GenParser tok st a -> GenParser tok st ()
skipMany p
  = do{ _ <- manyAccum (\x xs -> []) p
      ; return ()
      }

manyAccum :: (a -> [a] -> [a]) -> GenParser tok st a -> GenParser tok st [a]
manyAccum accum (Parser p)
  = Parser (\state ->
    let walk xs state r =
            case r of
            Empty (Error True err)     -> return (Error True err)
            Empty (Error False err)    -> return (Ok xs state err)
            Empty ok                   -> error "ParsecPrim.many: combinator 'many' is applied to a parser that accepts an empty string."
            Consumed (Error deadly err)-> return (Error deadly err)
            Consumed (Ok x state' err) ->
              do let ys = accum x xs
                 p_reply' <- p state'
                 seq ys (walk ys state' p_reply')
    in do p_reply <- p state
          case (p_reply) of
            Empty reply  -> case reply of
                              Ok x state' err -> error "ParsecPrim.many: combinator 'many' is applied to a parser that accepts an empty string."
                              Error True err  ->
                                return (Empty (Error True err))
                              Error False err ->
                                return (Empty (Ok [] state err))
            consumed     -> walk [] state consumed >>= return . Consumed)


-----------------------------------------------------------
-- Parsers unfolded for speed:
--  tokens
-----------------------------------------------------------

{- specification of @tokens@:
tokens showss nextposs s
  = scan s
  where
    scan []       = return s
    scan (c:cs)   = do{ token show nextpos c <?> shows s; scan cs }

    show c        = shows [c]
    nextpos pos c = nextposs pos [c]
-}

tokens :: Eq tok => ([tok] -> String) -> (Position -> [tok] -> Position)
       -> [tok] -> GenParser tok st [tok]
tokens shows nextposs s
    = Parser (\state@(State input pos user) ->
       let
        ok cs             = let newpos   = nextposs pos s
                                newstate = State cs newpos user
                            in seq newpos $ seq newstate $
                               return (Ok s newstate [])

        errEof            = Error False [errSyntaxEof pos [shows s]]
        errExpect c       = Error False [errSyntax pos (shows [c]) [shows s]]

        walk [] cs        = ok cs
        walk xs []        = return errEof
        walk (x:xs) (c:cs)| x == c        = walk xs cs
                          | otherwise     = return (errExpect c)

        walk1 [] cs        = fmap Empty (ok cs)
        walk1 xs []        = return (Empty errEof)
        walk1 (x:xs) (c:cs)| x == c        = fmap Consumed (walk xs cs)
                           | otherwise     = return (Empty (errExpect c))

       in walk1 s input)

errSyntax :: Position -> String -> [String] -> EMsg
errSyntax pos tok toks = (pos, ESyntax tok (nub $ filter (not . null) toks))
errSyntaxEof :: Position -> [String] -> EMsg
errSyntaxEof pos toks = (pos, ESyntax "end of file" (nub $ filter (not . null) toks))
