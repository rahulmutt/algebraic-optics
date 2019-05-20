-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Traversal
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Traversal where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Data.Int
import Data.Monoid
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.State

traversed :: Traversable t => AIndexedTraversal Int (t a) (t b) a b 
traversed = itraverseL

traversed64 :: Traversable t => AIndexedTraversal Int64 (t a) (t b) a b 
traversed64 = itraverseL

traverseL :: Traversable t => ATraversal (t a) (t b) a b 
traverseL sm = istateM (mapAccumLM accum mempty1)
  where accum gx a = do
          (gx', b) <- runIxStateT sm a 
          return (gx `mappend1` gx', b)

itraverseL :: (Traversable t, Integral n) => AIndexedTraversal n (t a) (t b) a b 
itraverseL sm = istateM (fmap (first fst) . mapAccumLM accum (mempty1, 0))
  where accum (gx, !n) a = do
          (gx', b) <- runIxReaderStateT sm n a
          return ((gx `mappend1` gx', n + 1), b)

mapMOf :: (IxMonadState n, IxMonadLift m n) => Traversal n s t a b -> (a -> m b) -> s -> m t
mapMOf hom f s = execIxStateT (hom (istateM (fmap (\b -> (First $ Just (), b)) . f))) s

mapAccumLM :: (Traversable t, Monad m) => (a -> b -> m (a, c)) -> a -> t b -> m (a, t c) 
mapAccumLM f a tb = fmap swap (runStateT (traverse g tb) a)
  where g b = do
          a <- get
          (a', c) <- lift (f a b)
          put a'
          return c
        swap (x, y) = (y, x)