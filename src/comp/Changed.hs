module Changed where

-- ============================================================
-- Changed flag wrapper

-- Changed flag type - Unchanged carries no payload for efficiency
-- Similar to Maybe but with "change tracking" semantics
-- Not an Applicative/Monad because Unchanged has no value to work with:
--   - Can't define: Changed f <*> Unchanged (no value to apply f to)
--   - Can't define: pure/return (unclear if should be Changed or Unchanged)
-- Lazy in 'a' to minimize peak memory residency (deepseq at top level handles forcing)
data Changed a = Changed a | Unchanged

-- Rebuild with 1 Changed argument
{-# INLINE changed1 #-}
changed1 :: (a -> b) -> Changed a -> Changed b
changed1 _ Unchanged = Unchanged
changed1 f (Changed x) = Changed (f x)

-- Get the value from Changed, or use the provided original if Unchanged
{-# INLINE changedOr #-}
changedOr :: a -> Changed a -> a
changedOr orig Unchanged = orig
changedOr _ (Changed x) = x

-- Rebuild with 2 Changed arguments - returns Unchanged only if both unchanged
{-# INLINE changed2 #-}
changed2 :: (a -> b -> c) -> a -> b -> Changed a -> Changed b -> Changed c
changed2 _     _     _ Unchanged    Unchanged    = Unchanged
changed2 f     _ origB (Changed a') Unchanged    = Changed $ f a' origB
changed2 f origA     _ Unchanged    (Changed b') = Changed $ f origA b'
changed2 f     _     _ (Changed a') (Changed b') = Changed $ f a' b'

-- Rebuild with 3 Changed arguments - returns Unchanged only if all unchanged
{-# INLINE changed3 #-}
changed3 :: (a -> b -> c -> d) -> a -> b -> c -> Changed a -> Changed b -> Changed c -> Changed d
changed3 _     _     _     _ Unchanged    Unchanged    Unchanged    = Unchanged
changed3 f     _ origB origC (Changed a') Unchanged    Unchanged    = Changed $ f a' origB origC
changed3 f origA     _ origC Unchanged    (Changed b') Unchanged    = Changed $ f origA b' origC
changed3 f origA origB     _ Unchanged    Unchanged    (Changed c') = Changed $ f origA origB c'
changed3 f     _     _ origC (Changed a') (Changed b') Unchanged    = Changed $ f a' b' origC
changed3 f     _ origB     _ (Changed a') Unchanged    (Changed c') = Changed $ f a' origB c'
changed3 f origA     _     _ Unchanged    (Changed b') (Changed c') = Changed $ f origA b' c'
changed3 f     _     _     _ (Changed a') (Changed b') (Changed c') = Changed $ f a' b' c'
