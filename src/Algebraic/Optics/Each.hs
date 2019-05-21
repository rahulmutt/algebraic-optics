-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Each
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Each where

import Algebraic.Optics.Traversal
import Algebraic.Optics.Type

import Data.List.NonEmpty
import Data.Functor.Identity

class Each s t a b | s -> a, t -> b, s b -> t, t a -> s where
    each :: Traversal s t a b

    default each :: (Traversable f, s ~ f a, t ~ f b) => Traversal s t a b
    each = traverseL
    {-# INLINE each #-}

instance Each [a] [b] a b
    
instance Each (NonEmpty a) (NonEmpty b) a b

instance Each (Identity a) (Identity b) a b

instance Each (Maybe a) (Maybe b) a b
