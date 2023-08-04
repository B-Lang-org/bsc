module VVerilogDollar (removeDollarsFromVerilog) where
import Id
import FStringCompat
import PreStrings (fsDollar)
import Verilog
import Data.Generics
import Control.Monad(guard)
import Control.Monad.State(State, gets, put, execState)
import qualified Data.Map as Map
import qualified Data.Set as Set
import ErrorUtil (internalError)

removeDollarsFromVerilog :: VProgram -> VProgram
removeDollarsFromVerilog vprog
  = let
        all_vids :: [VId]
        all_vids = get_vids vprog

        used_ids :: Used_RHS
        used_ids = set_of_used_ids all_vids

        the_map :: The_map
        the_map = get_map_ids used_ids all_vids
      in everywhere (mkT (new_vid the_map)) vprog

get_vids :: VProgram -> [VId]
get_vids vprog
  = listify
      (let
           tag :: VId -> Bool
           tag _ = True
         in tag)
      vprog

type The_map = Map.Map Id Id

type Used_RHS = Set.Set String

data S = S The_map Used_RHS

type M a = State S a

get_map :: S -> The_map
get_map s
  = case s of
        (S x _) -> x

get_used_underscore_identifiers :: S -> Used_RHS
get_used_underscore_identifiers s
  = case s of
        (S _ x) -> x

-- we check if the verilog has a dollar sign, and if it does,
-- process the internal id,
-- eventually regenerating from verilog name from the internal id
process_v_identifier :: VId -> M ()
process_v_identifier vid
  = let
        vid_string :: String
        vid_string = getVIdString vid
      in
      case (break_at_dollar_sign vid_string) of
          Nothing -> return ()
          _ -> let
                   the_id :: Id
                   the_id = vidToId (vid)
                 in
                 case ((/=) vid_string (getIdString (the_id))) of
                     True
                       -> internalError ((++) "vid string and id differ: " (show vid))
                     _ -> do used_underscore_ids <- (gets
                                                       get_used_underscore_identifiers)
                             the_map <- (gets get_map)
                             case (Map.lookup the_id the_map) of
                                 (Just _) -> return ()
                                 _ -> let
                                          id_possibilities :: [Id]
                                          id_possibilities
                                            = map (uncurry a_new_id) string_id_possibilities

-- I worry about the interaction of unsafePerformIO buried inside mkFString
-- and how it interacts with the infinite list being
-- created in id_possibilities.
                                          a_new_id :: String -> String -> Id
                                          a_new_id qual base
                                            = setIdQual (setIdBase the_id (mkFString base))
                                                (mkFString qual)

-- chooses one of the dollar signs in an id
-- and does the insertion of the separator.
-- The tuple elements are (qual,base).
                                          string_id_possibilities :: [(String, String)]
                                          string_id_possibilities
                                            = let
                                                  qual :: String
                                                  qual = getFString (getIdQual the_id)

                                                  base :: String
                                                  base = getFString (getIdBase the_id)

                                                  clean :: String -> [String]
                                                  clean s = repeat (replace_internal_dollars s)
                                                in
                                                case (break_at_dollar_sign base) of
                                                    (Just (left, right))
                                                      -> zip (clean qual)
                                                           (join_possibilities left right)
                                                    _ -> case (break_at_dollar_sign qual) of
                                                             (Just (left, right))
-- if a dollar sign occurs in a qualifier...?
-- Not sure what the correct thing to do is here.
-- Ravi hypothesizes that qualifiers are all empty strings by this phase.
                                                               -> zip
                                                                    (join_possibilities left right)
                                                                    (clean base)
                                                             Nothing
                                                               -> internalError
                                                                    ((++)
                                                                       "cannot find dollar sign in Id: "
                                                                       (show vid))

                                          good_id :: Id -> Bool
                                          good_id i
                                            = not (Set.member (getIdString i) used_underscore_ids)

                                          first_good_id :: Id
                                          first_good_id = head ((filter good_id) (id_possibilities))
                                        in
                                        put
                                          (S (Map.insert the_id first_good_id the_map)
                                             (Set.insert (getIdString first_good_id)
                                                used_underscore_ids))

new_vid :: The_map -> VId -> VId
new_vid m v
  = case v of
        (VId vid_string old_id item)
          -> case (break_at_dollar_sign vid_string) of
                 Nothing -> v
                 _ -> let
                          out_string :: String
                          out_string = getIdString my_new_id

                          my_new_id :: Id
                          my_new_id = new_id m old_id
                        in
                        case (break_at_dollar_sign out_string) of
                            (Just _) -> internalError "dollar removal did not work"
                            _ -> VId out_string my_new_id item

new_id :: The_map -> Id -> Id
new_id m i = Map.findWithDefault i i m

set_of_used_ids :: [VId] -> Used_RHS
set_of_used_ids s
  = let
        no_dollar :: String -> Bool
        no_dollar s
          = case (break_at_dollar_sign s) of
                Nothing -> True
                _ -> False
      in Set.fromList ((filter no_dollar) ((map getVIdString) (s)))

get_map_ids :: Used_RHS -> [VId] -> The_map
get_map_ids used s
  = get_map
      (execState (mapM_ process_v_identifier s) (S Map.empty used))

-- the list of possibilities of how to join x and y with a separator
-- for example, x_y, x_1y, x_2y, ...
join_possibilities :: String -> String -> [String]
join_possibilities x y
  = let
        j :: String -> String
        j sep = x ++ sep ++ y
      in map j join_separators

dollar_replacement :: String
dollar_replacement = "_"

-- this is the prefix of the separator string,
-- appended with 1,2,3,... used when regular underscore fails.
hard_dollar_replacement :: String
hard_dollar_replacement = dollar_replacement

join_separators :: [String]
join_separators
  = (:) dollar_replacement
      (map (((++) hard_dollar_replacement) . show)
         (enumFrom (1 :: Integer)))

break_at_dollar_sign :: String -> Maybe (String, String)
break_at_dollar_sign item
  = do guard (not (null (item)))
-- do not touch $display, etc.
       guard ((/=) (head item) '$')
       let
           splitted :: (String, String)
           splitted = break ((==) char_dollar) item

           left :: String
           left = fst splitted

-- remove both the head dollar sign
-- and replace additional internal dollar signs with underscores
           right :: String
           right = replace_internal_dollars (tail (snd (splitted)))
         in
         do guard (not (null (snd (splitted))))
-- only proceed if there is an internal dollar sign
            return (left, right)

char_dollar :: Char
char_dollar
  = case (getFString fsDollar) of
        ((:) c ([])) -> c
-- all the detection of fsDollar algorithms rely that it is a single character
        _ -> internalError "fsDollar is not a single character"

replace_internal_dollars :: String -> String
replace_internal_dollars s
  = do c <- s
       case ((==) c char_dollar) of
           True -> dollar_replacement
           _ -> [c]
