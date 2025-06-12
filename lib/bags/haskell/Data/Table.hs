{-# OPTIONS_GHC -Wno-dodgy-exports -Wno-unused-imports #-}

module Data.Table
    ( module Data.Table.Def
    , module Data.Table.Prop
      -- The above module does not export identifiers,
      -- but it does export Haddock documentation!
    ) where

import Data.Table.Def
import Data.Table.Prop
