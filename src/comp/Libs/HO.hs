-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module HO where

-- @@ Some useful combinators.

lift op f g = \ x -> f x `op` g x

cross f g = \ x -> (f x, g x)

apFst f (x, y) = (f x, y)

apSnd f (x, y) = (x, f y)

curry3 f x y z = f (x,y,z)

uncurry3 f ~(x,y,z) = f x y z

curry4 f x y z w = f (x,y,z,w)

uncurry4 f ~(x,y,z,w) = f x y z w
