> {-# LANGUAGE CPP #-}
> module Balanced(
>     Binding((:->)), key, prio, PSQ,
>     -- constructors and insertion
>     empty, single, insert, fromOrdList,
>     -- destructors and deletion
>     MinView(Empty, Min), minView, delete,
>     -- observers
>     lookup, toOrdList, atMost, atMostRange,
>     -- modifier
>     adjust)
> where
> import Prelude hiding (lookup

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)

>                       ,(<>)

#endif

>                       )
> import ErrorUtil(internalError)

 import Basic hiding (guard)
 import Sequ hiding (empty, single)
 import qualified Sequ

> infixr 5 <>


\paragraph{Constructors and insertion}

> empty                         :: PSQ k p
> single                        :: Binding k p -> PSQ k p
> insert                        :: (Ord k, Ord p) => Binding k p -> PSQ k p -> PSQ k p
> fromOrdList                   :: Ord p => [Binding k p] -> PSQ k p

\paragraph{Destructors and deletion}

> data MinView k p              =  Empty | Min (Binding k p) (PSQ k p)
> minView                       :: (Ord k, Ord p) => PSQ k p -> MinView k p
> delete                        :: (Ord k, Ord p) => k -> PSQ k p -> PSQ k p

\paragraph{Observer}

> lookup                        :: (Ord k, Ord p) => k -> PSQ k p -> Maybe p
> toOrdList                     :: (Ord k, Ord p) => PSQ k p -> [Binding k p]
> atMost                        :: Ord p => p -> PSQ k p -> [Binding k p]
> atMostRange                   :: (Ord k, Ord p) => p -> (k, k) -> PSQ k p -> [Binding k p]

\paragraph{Modifier}

> adjust                        :: (Ord k, Ord p) => (p -> p) -> k -> PSQ k p -> PSQ k p

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Implementation}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

Weight-balanced priority search pennants (based on Adams's weight-balanced
trees).

> data PSQ k p                  =  Void | Winner k p (LTree k p) k
>
> type Size                     =  Int
>
> data LTree k p                =  Start
>                               |  LLoser Size k p (LTree k p) k (LTree k p)
>                               |  RLoser Size k p (LTree k p) k (LTree k p)
>
> left, right                   :: LTree a b -> LTree a b
> left  Start                   =  internalError "left: empty loser tree"
> left  (LLoser _ _ _ tl _ _tr)        =  tl
> left  (RLoser _ _ _ tl _ _tr)        =  tl
> right Start                   =  internalError "right: empty loser tree"
> right (LLoser _ _ _ _tl _ tr)        =  tr
> right (RLoser _ _ _ _tl _ tr)        =  tr

> maxKey                        :: PSQ k p -> k
> maxKey Void                   =  internalError "maxKey: empty queue"
> maxKey (Winner _k _p _t m)    =  m

Smart constructors.

> start                         :: LTree k p
> start                                =  Start
>
> lloser, rloser                :: k -> p -> LTree k p -> k -> LTree k p -> LTree k p
> lloser k p tl m tr                =  LLoser (1 + size tl + size tr) k p tl m tr
> rloser k p tl m tr                =  RLoser (1 + size tl + size tr) k p tl m tr
>
> size                          :: LTree k p -> Size
> size Start                    =  0
> size (LLoser s _ _ _ _ _)     =  s
> size (RLoser s _ _ _ _ _)     =  s

\paragraph{Balancing}

Balance factor.

> omega                                :: Int
> omega                                =  2

> lbalance, rbalance           :: Ord p => k -> p -> LTree k p -> k -> LTree k p -> LTree k p
> lbalance k p l m r
>   | size l + size r < 2       =  lloser        k p l m r
>   | size r > omega * size l   =  lbalanceLeft  k p l m r
>   | size l > omega * size r   =  lbalanceRight k p l m r
>   | otherwise                 =  lloser        k p l m r
>
> rbalance k p l m r
>   | size l + size r < 2       =  rloser        k p l m r
>   | size r > omega * size l   =  rbalanceLeft  k p l m r
>   | size l > omega * size r   =  rbalanceRight k p l m r
>   | otherwise                 =  rloser        k p l m r

> lbalanceLeft  k p l m r
>   | size (left r) < size (right r)        =  lsingleLeft  k p l m r
>   | otherwise                         =  ldoubleLeft  k p l m r
> lbalanceRight k p l m r
>   | size (right l) < size (left l)        =  lsingleRight k p l m r
>   | otherwise                         =  ldoubleRight k p l m r
>
> rbalanceLeft  k p l m r
>   | size (left r) < size (right r)        =  rsingleLeft  k p l m r
>   | otherwise                         =  rdoubleLeft  k p l m r
> rbalanceRight k p l m r
>   | size (right l) < size (left l)    =  rsingleRight k p l m r
>   | otherwise                         =  rdoubleRight k p l m r

> lsingleLeft k1 p1 t1 m1 (LLoser _ k2 p2 t2 m2 t3)
>   | p1 <= p2                        =  lloser k1 p1 (rloser k2 p2 t1 m1 t2) m2 t3
>   | otherwise                        =  lloser k2 p2 (lloser k1 p1 t1 m1 t2) m2 t3
> lsingleLeft k1 p1 t1 m1 (RLoser _ k2 p2 t2 m2 t3)
>                                =  rloser k2 p2 (lloser k1 p1 t1 m1 t2) m2 t3
> lsingleLeft _ _ _ _ Start = internalError "lsingleLeft"
>
> rsingleLeft k1 p1 t1 m1 (LLoser _ k2 p2 t2 m2 t3)
>                                =  rloser k1 p1 (rloser k2 p2 t1 m1 t2) m2 t3
> rsingleLeft k1 p1 t1 m1 (RLoser _ k2 p2 t2 m2 t3)
>                                =  rloser k2 p2 (rloser k1 p1 t1 m1 t2) m2 t3
> rsingleLeft _ _ _ _ Start = internalError "rsingleLeft"
>
> lsingleRight k1 p1 (LLoser _ k2 p2 t1 m1 t2) m2 t3
>                                =  lloser k2 p2 t1 m1 (lloser k1 p1 t2 m2 t3)
> lsingleRight k1 p1 (RLoser _ k2 p2 t1 m1 t2) m2 t3
>                                =  lloser k1 p1 t1 m1 (lloser k2 p2 t2 m2 t3)
> lsingleRight _ _ Start _ _ = internalError "lsingleRight"
>
> rsingleRight k1 p1 (LLoser _ k2 p2 t1 m1 t2) m2 t3
>                                =  lloser k2 p2 t1 m1 (rloser k1 p1 t2 m2 t3)
> rsingleRight k1 p1 (RLoser _ k2 p2 t1 m1 t2) m2 t3
>   | p1 <= p2                        =  rloser k1 p1 t1 m1 (lloser k2 p2 t2 m2 t3)
>   | otherwise                        =  rloser k2 p2 t1 m1 (rloser k1 p1 t2 m2 t3)
> rsingleRight _ _ Start _ _ = internalError "rsingleRight"

> ldoubleLeft k1 p1 t1 m1 (LLoser _ k2 p2 t2 m2 t3)
>                               =  lsingleLeft k1 p1 t1 m1 (lsingleRight k2 p2 t2 m2 t3)
> ldoubleLeft k1 p1 t1 m1 (RLoser _ k2 p2 t2 m2 t3)
>                               =  lsingleLeft k1 p1 t1 m1 (rsingleRight k2 p2 t2 m2 t3)
> ldoubleLeft _ _ _ _ Start = internalError "ldoubleLeft"
>
> ldoubleRight k1 p1 (LLoser _ k2 p2 t1 m1 t2) m2 t3
>                               =  lsingleRight k1 p1 (lsingleLeft k2 p2 t1 m1 t2) m2 t3
> ldoubleRight k1 p1 (RLoser _ k2 p2 t1 m1 t2) m2 t3
>                               =  lsingleRight k1 p1 (rsingleLeft k2 p2 t1 m1 t2) m2 t3
> ldoubleRight _ _ Start _ _ = internalError "ldoubleRight"
>
> rdoubleLeft k1 p1 t1 m1 (LLoser _ k2 p2 t2 m2 t3)
>                               =  rsingleLeft k1 p1 t1 m1 (lsingleRight k2 p2 t2 m2 t3)
> rdoubleLeft k1 p1 t1 m1 (RLoser _ k2 p2 t2 m2 t3)
>                               =  rsingleLeft k1 p1 t1 m1 (rsingleRight k2 p2 t2 m2 t3)
> rdoubleLeft _ _ _ _ Start = internalError "rdoubleLeft"
>
> rdoubleRight k1 p1 (LLoser _ k2 p2 t1 m1 t2) m2 t3
>                               =  rsingleRight k1 p1 (lsingleLeft k2 p2 t1 m1 t2) m2 t3
> rdoubleRight k1 p1 (RLoser _ k2 p2 t1 m1 t2) m2 t3
>                               =  rsingleRight k1 p1 (rsingleLeft k2 p2 t1 m1 t2) m2 t3
> rdoubleRight _ _ Start _ _ = internalError "rdoubleRight"

\paragraph{Playing a match}

> play                          :: Ord p => PSQ k p -> PSQ k p -> PSQ k p
> Void `play` t'                =  t'
> t `play` Void                 =  t
> Winner k p t m  `play`  Winner k' p' t' m'
>   | p <= p'                   =  Winner k  p  (rbalance k' p' t m t') m'
>   | otherwise                 =  Winner k' p' (lbalance k  p  t m t') m'

Note that this is the only place where |lbalance| and |rbalance| are used.

> unsafePlay                    :: Ord p => PSQ k p -> PSQ k p -> PSQ k p
> Void `unsafePlay` t'          =  t'
> t `unsafePlay` Void           =  t
> Winner k p t m  `unsafePlay`  Winner k' p' t' m'
>   | p <= p'                   =  Winner k  p  (rbalance k' p' t m t') m'
>   | otherwise                 =  Winner k' p' (lbalance k  p  t m t') m'

The unsafe function |unsafePlay| can be used instead of |play| if we
know that the shape of the tree has not changed or if the tree is
known to be balanced.

Tournament view.
%if False

{- #INLINE tourView #-}

%endif

> data TourView k p             =  Null | Single k p | Play (PSQ k p) (PSQ k p)
>
> tourView                      :: PSQ k p -> TourView k p
> tourView Void                 =  Null
> tourView (Winner k p Start _m)=  Single k p
> tourView (Winner k p (RLoser _ k' p' tl m tr) m')
>                               =  Winner k  p  tl m `Play` Winner k' p' tr m'
> tourView (Winner k p (LLoser _ k' p' tl m tr) m')
>                               =  Winner k' p' tl m `Play` Winner k  p  tr m'

\paragraph{Constructors and insertion}

> empty                         =  Void
>
> single (k :-> p)              =  single' k p
>
> single'                        :: k -> p -> PSQ k p
> single' k p                        =  Winner k p start k
>
> insert b q                    =  case tourView q of
>   Null                        -> single b
>   Single k' p'
>     | key b <  k'             -> single b      `play` single' k' p'
>     | key b == k'             -> single b
>     | otherwise               -> single' k' p' `play` single b
>   tl `Play` tr
>     | key b <= maxKey tl      -> insert b tl `play` tr
>     | otherwise               -> tl `play` insert b tr
>
> fromOrdList                   =  foldm unsafePlay empty . map single

\paragraph{Destructors and deletion}

> minView Void                  =  Empty
> minView (Winner k p t m)      =  Min (k :-> p) (secondBest t m)
>
> delete k q                    =  case tourView q of
>   Null                        -> empty
>   Single k' p
>     | k == k'                 -> empty
>     | otherwise               -> single' k' p
>   tl `Play` tr
>     | k <= maxKey tl          -> delete k tl `play` tr
>     | otherwise               -> tl `play` delete k tr

Determining the second-best player.

> secondBest                    :: (Ord k, Ord p) => LTree k p -> k -> PSQ k p
> secondBest Start _m           =  Void
> secondBest (LLoser _ k p tl m tr) m'
>                                   =  Winner k p tl m `play` secondBest tr m'
> secondBest (RLoser _ k p tl m tr) m'
>                                  =  secondBest tl m `play` Winner k p tr m'

\paragraph{Observers}

> lookup k q                    =  case tourView q of
>   Null                        -> Nothing
>   Single k' p
>     | k == k'                 -> Just p
>     | otherwise               -> Nothing
>   tl `Play` tr
>     | k <= maxKey tl          -> lookup k tl
>     | otherwise               -> lookup k tr
>
> toOrdList q                   =  toList (toOrdLists q)
>
> toOrdLists                    :: (Ord k, Ord p) => PSQ k p -> Sequ (Binding k p)
> toOrdLists q                  =  case tourView q of
>   Null                        -> s_empty
>   Single k p                  -> s_single (k :-> p)
>   tl `Play` tr                -> toOrdLists tl <> toOrdLists tr
>
> atMost pt q                        =  toList (atMosts pt q)
>
> atMosts                       :: Ord p => p -> PSQ k p -> Sequ (Binding k p)
> atMosts _pt Void              =  s_empty
> atMosts pt (Winner k p t _)   =  prune k p t
>   where
>   prune k p t
>     | p > pt                    =  s_empty
>     | otherwise               =  traverse k p t
>   traverse k p Start          =  s_single (k :-> p)
>   traverse k p (LLoser _ k' p' tl _m tr)
>                                     =  prune    k' p' tl <> traverse k  p  tr
>   traverse k p (RLoser _ k' p' tl _m tr)
>                               =  traverse k  p  tl <> prune    k' p' tr
>
>
> atMostRange pt (kl, kr) q        =  toList (atMostRanges pt (kl, kr) q)

> atMostRanges                  :: (Ord k, Ord p) => p -> (k, k) -> PSQ k p -> Sequ (Binding k p)
> atMostRanges _pt _range Void =  s_empty
> atMostRanges pt range@(kl, kr) (Winner k p t _)
>                              =  prune k p t
>   where
>   prune k p t
>     | p > pt                        =  s_empty
>     | otherwise               =  traverse k p t
>   traverse k p Start
>     | k `inrange` range        =  s_single (k :-> p)
>     | otherwise               =  s_empty
>   traverse k p (LLoser _ k' p' tl m tr)
>                               =  guard (kl <= m) (prune    k' p' tl)
>                               <> guard (m <= kr) (traverse k  p  tr)
>   traverse k p (RLoser _ k' p' tl m tr)
>                                     =  guard (kl <= m) (traverse k  p  tl)
>                               <> guard (m <= kr) (prune    k' p' tr)

\paragraph{Modifier}

> adjust f k q                  =  case tourView q of
>   Null                        -> empty
>   Single k' p
>     | k == k'                 -> single' k' (f p)
>     | otherwise               -> single' k' p
>   tl `Play` tr
>     | k <= maxKey tl          -> adjust f k tl `unsafePlay` tr
>     | otherwise               -> tl `unsafePlay` adjust f k tr

--------------- Basic ---------------

> data Binding k p              =  k :-> p
>     deriving(Show)
>
> key                           :: Binding k p -> k
> key  (k :-> _p)               =  k
>
> prio                          :: Binding k p -> p
> prio (_k :-> p)               =  p

Folding a list in a binary-subdivision scheme.

> foldm                         :: (a -> a -> a) -> a -> [a] -> a
> foldm (*) e x
>   | null x                    =  e
>   | otherwise                 =  fst (rec (length x) x)
>   where rec 1 (a : as)        =  (a, as)
>         rec n as              =  (a1 * a2, as2)
>           where m             =  n `div` 2
>                 (a1, as1)     =  rec (n - m) as
>                 (a2, as2)     =  rec m       as1

> inrange                        :: (Ord a) => a -> (a, a) -> Bool
> a `inrange` (l, r)                =  l <= a && a <= r

--------------- Sequ ---------------

> s_empty                       :: Sequ a
>
> s_single                      :: a -> Sequ a
>
> (<>)                          :: Sequ a -> Sequ a -> Sequ a
>
> -- fromList                      :: [a] -> Sequ a
>
> -- fromListT                     :: ([a] -> [a]) -> Sequ a
>
> toList                        :: Sequ a -> [a]

% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Implementation}
% - - - - - - - - - - - - - - - = - - - - - - - - - - - - - - - - - - - - - - -

> {-
> newtype Sequ a                =  Sequ ([a] -> [a])
>
> s_empty                       =  Sequ (\as -> as)
>
> s_single a                    =  Sequ (\as -> a : as)
>
> Sequ x1 <> Sequ x2            =  Sequ (\as -> x1 (x2 as))
>
> fromList as                   =  Sequ (\as' -> as ++ as')
>
> -- fromListT as                  =  Sequ as
>
> toList (Sequ x)               =  x []
> -}
>
> data Sequ a                        =  SEmpty | SUnit a | SFork (Sequ a) (Sequ a)
>
> s_empty                       =  SEmpty
>
> s_single a                    =  SUnit a
>
> x1 <> x2                         =  SFork x1 x2
>
> -- fromList xs                   =  foldr (<>) SEmpty (map s_single xs)
>
> toList as                     =  acc as []
>   where acc SEmpty r = r
>         acc (SUnit x) r = x : r
>         acc (SFork s1 s2) r = acc s1 (acc s2 r)
>


> instance Show a => Show (Sequ a) where
>     showsPrec d a             =  showsPrec d (toList a)

Derived function(s).

> guard                         :: Bool -> Sequ a -> Sequ a
> guard False _as               =  s_empty
> guard True  as                =  as
