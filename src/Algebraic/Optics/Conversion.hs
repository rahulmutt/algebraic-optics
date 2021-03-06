-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Conversion
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Conversion where

import Algebraic.Optics.Type
-- import Algebraic.Optics.Internal.Indexed

fromVL :: (forall f. (Functor f) => (a -> f b) -> (s -> f t)) -> Lens s t a b
fromVL _lens _sm = undefined -- TODO: istateM (lens (runIxStateT sm))