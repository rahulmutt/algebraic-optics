-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Iso
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Iso where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

iso :: (s -> a) -> (b -> t) -> Iso s t a b 
iso f g sm = 
    istateM $ \s -> do
        (r, b) <- runIxStateT sm (f s)
        return (r, g b)