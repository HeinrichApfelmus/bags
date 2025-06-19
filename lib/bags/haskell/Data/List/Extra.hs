module Data.List.Extra where

import Numeric.Natural

replicateNat :: Natural -> a -> [a]
replicateNat 0 _ = []
replicateNat n x = x : replicateNat (n-1) x
