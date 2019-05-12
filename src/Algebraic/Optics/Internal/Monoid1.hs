-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Internal.Monoid1
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Internal.Monoid1 where

import GHC.TypeLits hiding (Nat)
import Data.Functor.Identity
import Data.Monoid
import Data.Functor.Const

class Monoid1 m where
    mempty1 :: m a
    mappend1 :: m a -> m a -> m a

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
    => Monoid1 Identity where
    mempty1 = undefined
    mappend1 = undefined

instance Monoid1 Endo where
    mempty1 = mempty
    mappend1 = mappend

instance Monoid1 First where
    mempty1 = mempty
    mappend1 = mappend

instance (Monoid m) => Monoid1 (Const m) where
    mempty1 = mempty
    mappend1 = mappend