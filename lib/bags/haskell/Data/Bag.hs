{-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}

module Data.Bag 
    (
    -- * Type and Definitional Properties
    Bag,
    singleton,
    foldBag,
    -- * Operations
    -- ** Query
    null,
    mnull,
    size,
    msize,
    count,
    member,
    mmember,
    -- ** Construction
    fromMaybe,
    fromList,
    -- ** Deletion
    deleteOne,
    -- $prop-deleteOne-member-True
    
    -- $prop-deleteOne-member-False
    
    -- ** Combine
    union,
    cartesianProduct,
    equijoin,
    -- ** Traversal
    map,
    concatMap,
    filter,
    -- * Properties
    module Data.Bag.Prop,
    module Data.Bag.Prop.Deletion,
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap)


import Data.Bag.Def
import Data.Bag.Quotient
import Data.Bag.Found (deleteOne)
import Data.Bag.Prop
import Data.Bag.Prop.Deletion

