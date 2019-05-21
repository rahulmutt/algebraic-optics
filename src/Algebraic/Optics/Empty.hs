-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Empty
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Empty where

import Algebraic.Optics.Prism
import Algebraic.Optics.Type

class AsEmpty a where
    _Empty :: Prism' a ()

    default _Empty :: (Monoid a, Eq a) => Prism' a ()
    _Empty = prism (const mempty) 
                   (\a -> if a == mempty
                          then Right ()
                          else Left a)