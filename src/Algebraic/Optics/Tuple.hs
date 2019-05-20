-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Tuple
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Tuple where

import Algebraic.Optics.Lens
import Algebraic.Optics.Type

class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _1 :: ALens s t a b

instance Field1 (a, b) (a', b) a a' where
  _1 = lens fst (\(_, b) a' -> (a', b))

class Field2 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _2 :: ALens s t a b

instance Field2 (a, b) (a, b') b b' where
  _2 = lens snd (\(a, _) b' -> (a, b'))