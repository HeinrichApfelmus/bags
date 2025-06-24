{-# OPTIONS_GHC -Wno-dodgy-exports -Wno-unused-imports #-}

module Data.Table
    (
    -- * Type
    Table,
    -- * Operations
    -- ** Query
    lookup,
    elements,
    getMap,
    -- ** Construction
    singleton,
    indexBy,
    -- ** Combine
    merge,
    -- ** Conversion
    fromMap,
    fromSingletonsMap,

    -- * Properties
    module Data.Table.Prop
      -- The above module does not export identifiers,
      -- but it does export Haddock documentation!
    ) where

import Prelude hiding (lookup)

import Data.Table.Def
import Data.Table.Prop
