{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SchedInfo (
                  SchedInfo(..),

                  MethodConflictOp(..),
                  MethodConflictInfo(..),

                  makeMethodConflictDocs,

                  -- this is needed by BinData, for storing the contents
                  extractFromMethodConflictInfo,
                  -- these are needed only to support the scheduling pragma
                  mapMethodConflictInfo,
                  concatMapMethodConflictInfo,
                  filterMethodConflictInfo
                  ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(foldl',sortBy)
import PFPrint
import Eval
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Generics as Generic

-- ========================================================================
-- SchedInfo

data SchedInfo idtype = SchedInfo {
        methodConflictInfo :: MethodConflictInfo idtype,
        -- methods which have a rule that must execute between them
        -- (in the given order) and the list of rules
        -- XXX should we include the rule names?  they don't exist
        -- XXX on the boundary, but could be useful for debugging
        rulesBetweenMethods :: [((idtype, idtype), [idtype])],
        -- methods which have a rule that must execute before it
        -- along with the list of rules involved.
        -- Left  = rule directly before this method
        -- Right = method called by this method which requires a rule before it
        rulesBeforeMethods :: [(idtype,[Either idtype idtype])],
        -- methods which allow an unsynchronized clock domain crossing
        clockCrossingMethods :: [idtype]
        }
        deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

instance (PPrint idtype, Ord idtype) => PPrint (SchedInfo idtype) where
    pPrint d p si =
        sep [text "SchedInfo",
             pPrint d 0 (methodConflictInfo si),
             pPrint d 0 (rulesBetweenMethods si),
             pPrint d 0 (rulesBeforeMethods si),
             pPrint d 0 (clockCrossingMethods si)]

instance (PVPrint idtype, Ord idtype) => PVPrint (SchedInfo idtype) where
    pvPrint d p si =
        sep [text "SchedInfo",
             pvPrint d 0 (methodConflictInfo si),
             pvPrint d 0 (rulesBetweenMethods si),
             pvPrint d 0 (rulesBeforeMethods si),
             pvPrint d 0 (clockCrossingMethods si)]

instance (NFData idtype) => NFData (SchedInfo idtype) where
    rnf si = rnf4 (methodConflictInfo si)
                  (rulesBetweenMethods si)
                  (rulesBeforeMethods si)
                  (clockCrossingMethods si)

-- ========================================================================
-- MethodConflictOp
--

data MethodConflictOp = CF | SB | ME | P | SBR | C | EXT
       deriving (Eq, Ord)

instance Show MethodConflictOp where
   show CF = "CF"
   show SB = "SB"
   show ME = "ME"
   show P  = "P"
   show SBR = "SBR"
   show C = "C"
   show EXT = "EXT"

-- ========================================================================
-- MethodConflictInfo
--

{- a CF b     => a & b have the same effect when executed in parallel
                 in the same rule, or when executed in either order
                 in different rules in the same cycle.
   a SB b     => a & b have the same effect when executed in parallel
                 in the same rule, or when a is executed before b in
                 different rules in the same cycle.  Executing b before
                 a within one cycle is illegal.
   ME [a,b,c] => only one of a,b or c can execute in any cycle.
   a P b      => a & b may be executed in parallel within a single
                 rule.  It is illegal to execute a & b in the same
                 cycle in two different rules, in any order.
   a SBR b    => a may be executed before b in different rules in
                 the same cycle.  It is illegal to execute a & b in
                 parallel in a single rule, or to execute b before a
                 in two different rules in the same cycle.
   a C b      => a & b may not execute in the same cycle, whether in
                 one rule or two, in any order.
   EXT a      => two executions of a cannot occur in one rule.
                 a & b can execute in two different rules in the same
                 cycle but the effect will be different.  The
                 difference must be resolved external to the module.
-}

data MethodConflictInfo idtype =
    MethodConflictInfo {
        sCF  :: [(idtype, idtype)],
        sSB  :: [(idtype, idtype)],
        sME  :: [[idtype]],
        sP   :: [(idtype, idtype)],
        sSBR :: [(idtype, idtype)],
        sC   :: [(idtype, idtype)],
        sEXT :: [idtype]
    }
    deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

-- --------------------

instance (PPrint idtype, Ord idtype) => PPrint (MethodConflictInfo idtype) where
    pPrint d p mci =
        let ds = makeMethodConflictDocs (pPrint d p) ppReadable "[" "]" mci
        in  text "[" <> sepList ds (text ",") <> text "]"

instance (PVPrint idtype, Ord idtype) => PVPrint (MethodConflictInfo idtype) where
    pvPrint d p mci  =
        let ds = makeMethodConflictDocs (pvPrint d p) pvpReadable "[" "]" mci
        in  text "[" <> sepList ds (text ",") <> text "]"


-- Given:
--   * a printing function for ids (pPrint or pvPrint)
--   * a function for turning the ids into strings for sorting order
--   * start and stop enclosure for a list (we assume comma-separated)
--   * a MethodConflictInfo structure
-- Produce:
--   a list of Doc for the MethodConflictInfo info
--   (un-factored from pairs to groups)
--
makeMethodConflictDocs :: (Ord idtype) =>
                          (idtype -> Doc) ->
                          (idtype -> String) ->
                          String -> String ->
                          MethodConflictInfo idtype -> [Doc]
makeMethodConflictDocs pId sId listStart listEnd
        (MethodConflictInfo { sCF=sCF0, sSB=sSB0, sME=sME0, sP=sP0,
                              sSBR=sSBR0, sC=sC0, sEXT=sEXT0 }) =
    [pp m <+> text "CF"  <+> pp m' | (m,m') <- toPairsOfLists sCF0  ] ++
    [pp m <+> text "SB"  <+> pp m' | (m,m') <- toPairsOfLists sSB0  ] ++
    [         text "ME"  <+> pp m  |  m     <- sME_ordered          ] ++
    [pp m <+> text "P"   <+> pp m' | (m,m') <- toPairsOfLists sP0   ] ++
    [pp m <+> text "SBR" <+> pp m' | (m,m') <- toPairsOfLists sSBR0 ] ++
    [pp m <+> text "C"   <+> pp m' | (m,m') <- toPairsOfLists sC0   ] ++
    (if null sEXT0 then [] else [text "EXT" <+> pp sEXT_ordered])
  where
      pp [m] = pId m
      pp ms  =
          text listStart <> (sepList (map pId ms) (text ",")) <> text listEnd

      collect ps = M.fromListWith (S.union) [(a,S.singleton b) | (a,b) <- ps]
      toPairsOfLists ps = let m1 = collect ps
                              m2 = collect [(s,a) | (a,s) <- M.toList m1]
                          in sortLP [ (sortI (S.toList s2), sortI (S.toList s1))
                                    | (s1,s2) <- M.toList m2
                                    ]

      sortI  = sortBy (\ i1 i2 -> (sId i1) `compare` (sId i2))
      sortL  = sortBy (\ is1 is2 -> (map sId is1) `compare` (map sId is2))
      sortLP = sortBy (\(is1,_) (is2,_) -> (map sId is1) `compare` (map sId is2))
      sME_ordered  = sortL (map sortI sME0)
      sEXT_ordered = sortI sEXT0

-- --------------------

mapMethodConflictInfo :: (a -> b) ->
                         MethodConflictInfo a -> MethodConflictInfo b
mapMethodConflictInfo f x =
    let
        f2 (x1,x2) = (f x1, f x2)
        nsCF = (map f2 (sCF x))
        nsSB = (map f2 (sSB x))
        nsME = (map (map f) (sME x))
        nsP  = (map f2 (sP x))
        nsSBR= (map f2 (sSBR x))
        nsC  = (map f2 (sC x))
        nsEXT= (map f (sEXT x))
    in
        MethodConflictInfo {
            sCF  = nsCF,
            sSB  = nsSB,
            sME  = nsME,
            sP   = nsP,
            sSBR = nsSBR,
            sC   = nsC,
            sEXT = nsEXT
        }

concatMapMethodConflictInfo ::  (a -> [b]) ->
                                MethodConflictInfo a -> MethodConflictInfo b
concatMapMethodConflictInfo f x =
    let
        f2 z = [(tx,ty) | (x,y) <- z,
                          tx <- f x,
                          ty <- f y]

        nsCF = f2 (sCF x)
        nsSB = f2 (sSB x)
        nsME = (map (concatMap f) (sME x))
        nsP  = f2 (sP x)
        nsSBR= f2 (sSBR x)
        nsC  = f2 (sC x)
        nsEXT= (concatMap f (sEXT x))
    in
        MethodConflictInfo {
            sCF  = nsCF,
            sSB  = nsSB,
            sME  = nsME,
            sP   = nsP,
            sSBR = nsSBR,
            sC   = nsC,
            sEXT = nsEXT
        }

filterMethodConflictInfo :: Eq a => (a -> Bool) ->
                            MethodConflictInfo a -> MethodConflictInfo a
filterMethodConflictInfo f x =
    let
        f2 (x,y) = (f x) || (f y)

        nsCF = filter f2 (sCF x)
        nsSB = filter f2 (sSB x)
        nsME = filter ( /= []) (map (filter f) (sME x))
        nsP  = filter f2 (sP x)
        nsSBR= filter f2 (sSBR x)
        nsC  = filter f2 (sC x)
        nsEXT= (filter f (sEXT x))
    in
        MethodConflictInfo {
            sCF  = nsCF,
            sSB  = nsSB,
            sME  = nsME,
            sP   = nsP,
            sSBR = nsSBR,
            sC   = nsC,
            sEXT = nsEXT
        }

extractFromMethodConflictInfo :: Ord a => MethodConflictInfo a -> [a]
extractFromMethodConflictInfo x =
    let
        f s (x,y) = S.insert x (S.insert y s)
        setCF = foldl' f S.empty (sCF x)
        setSB = foldl' f S.empty (sSB x)
        setME = S.fromList (concat (sME x))
        setP  = foldl' f S.empty (sP x)
        setSBR= foldl' f S.empty (sSBR x)
        setC  = foldl' f S.empty (sC x)
        setEXT= S.fromList (sEXT x)
    in S.toList (S.unions [setCF, setSB, setME, setP, setSBR, setC, setEXT])

-- --------------------

instance (NFData idtype) => NFData (MethodConflictInfo idtype) where
    rnf (MethodConflictInfo { sCF=cf, sSB=sb, sME=me, sP=p,
                              sSBR=sbr, sC=c, sEXT=ext }) =
        rnf7 cf sb me p sbr c ext

-- ========================================================================
