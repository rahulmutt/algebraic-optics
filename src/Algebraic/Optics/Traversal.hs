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
import Data.Traversable
import Control.Arrow
import Control.Monad.Reader

traversed :: (Traversable t) => AIndexedTraversal Int (t a) (t b) a b 
traversed = itraverseL

traversed64 :: (Traversable t) => AIndexedTraversal Int64 (t a) (t b) a b 
traversed64 = itraverseL

traverseL :: (Traversable t) => ATraversal (t a) (t b) a b 
traverseL sm = istate (mapAccumL accum mempty1)
  where accum gx a = (gx `mappend1` gx', b)
          where (gx', b) = runIxState sm a 

itraverseL :: (Traversable t, Integral n) => AIndexedTraversal n (t a) (t b) a b 
itraverseL sm = istate (first fst . mapAccumL accum (mempty1, 0))
  where accum (gx, !n) a = ((gx `mappend1` gx', n + 1), b)
          where (gx', b) = runReader (runIxStateT sm a) n 