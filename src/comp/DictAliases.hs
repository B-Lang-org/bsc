module DictAliases(
    dictAlias,
    splitDictAliases
    ) where

import Data.List(partition)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import CSyntax
import ErrorUtil(internalError)
import Id
import PPrint(ppReadable)

-- A solved dictionary binding can be forwarding rather than evidence in its
-- own right.  Keep this deliberately narrower than the old CSubst-based
-- simplifier: a type application is real syntax, even when its head is a
-- variable, and must not be discarded here.
type DictAliases = M.Map Id Id

dictAlias :: CDefl -> Maybe (Id, Id)
dictAlias (CLValueSign
             (CDefT source [] (CQType [] _)
               [CClause [] [] (CVar target)]) [])
  | isDictId source && isDictId target = Just (source, target)
dictAlias _ = Nothing

closeDictAliases :: [(Id, Id)] -> DictAliases
closeDictAliases pairs = L.foldl' closeSource M.empty (M.keys raw)
  where
    raw = L.foldl' addPair M.empty pairs

    addPair m (source, target)
      | M.member source m =
          internalError ("duplicate dictionary forwarding source: " ++
                         ppReadable source)
      | otherwise = M.insert source target m

    closeSource memo source = snd (resolve S.empty memo source)

    resolve seen memo current
      | current `S.member` seen =
          internalError ("dictionary forwarding cycle: " ++
                         ppReadable (S.toList seen, current))
      | Just terminal <- M.lookup current memo = (terminal, memo)
      | Just next <- M.lookup current raw =
          let (terminal, memo') = resolve (S.insert current seen) memo next
          in  (terminal, M.insert current terminal memo')
      | otherwise = (current, memo)

-- Return a transitively closed forwarding map.  Retaining the terminal Id
-- value from the final edge preserves its properties; Id equality alone does
-- not carry all of that information.
dictAliases :: [CDefl] -> DictAliases
dictAliases ds = closeDictAliases pairs
  where
    pairs = [ pair | Just pair <- map dictAlias ds ]

splitDictAliases :: [CDefl] -> (DictAliases, [CDefl])
splitDictAliases ds = (dictAliases aliases, others)
  where
    (aliases, others) = partition isAlias ds
    isAlias d = case dictAlias d of
                  Just _  -> True
                  Nothing -> False
