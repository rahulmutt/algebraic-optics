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
import Data.Functor.Identity
import Data.Monoid
import Control.Arrow
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

traversed :: Traversable t => IndexedTraversal Int (t a) (t b) a b 
traversed = itraverseL

traversed64 :: Traversable t => IndexedTraversal Int64 (t a) (t b) a b 
traversed64 = itraverseL

traverseL :: Traversable t => Traversal (t a) (t b) a b 
traverseL sm = istateM (mapAccumLM accum mempty1)
  where accum gx a = do
          (gx', b) <- runIxStateT sm a 
          return (gx `mappend1` gx', b)

itraverseL :: (Traversable t, Integral n) => IndexedTraversal n (t a) (t b) a b 
itraverseL sm = istateM (fmap (first fst) . mapAccumLM accum (mempty1, 0))
  where accum (gx, !n) a = do
          (gx', b) <- runIxReaderStateT sm n a
          return ((gx `mappend1` gx', n + 1), b)

element :: Traversable t => Int -> IndexedTraversal' Int (t a) a
element i = elements (== i)

elements :: Traversable t => (Int -> Bool) -> IndexedTraversal' Int (t a) a
elements f sm = istateM (fmap (first fst) . mapAccumLM accum (mempty1, 0))
  where accum (gx, !n) a 
          | f n = do
            (gx', b) <- runIxReaderStateT sm n a
            return ((gx `mappend1` gx', n + 1), b)
          | otherwise = return ((gx, n + 1), a)

-- TODO: Make this support applicatives as well
traverseOf :: (IxMonadState n, IxMonadLift m n) => ATraversal m Unit n s t a b -> (a -> m b) -> s -> m t
traverseOf = mapMOf

forOf :: (IxMonadState n, IxMonadLift m n) => ATraversal m Unit n s t a b -> s -> (a -> m b) -> m t
forOf hom s f = traverseOf hom f s

-- TODO: Make this support applicatives as well
sequenceAOf :: (IxMonadState n, IxMonadLift f n) => ATraversal f Unit n s t (f b) b -> s -> f t  
sequenceAOf = sequenceOf

mapMOf :: (IxMonadState n, IxMonadLift m n) => ATraversal m Unit n s t a b -> (a -> m b) -> s -> m t
mapMOf hom f s = execIxStateT (hom (istateM (fmap (\b -> (pure (), b)) . f))) s

forMOf :: (IxMonadState n, IxMonadLift m n) => ATraversal m Unit n s t a b -> s -> (a -> m b) -> m t
forMOf hom s f = mapMOf hom f s

sequenceOf :: (IxMonadState n, IxMonadLift f n) => ATraversal f Unit n s t (f b) b -> s -> f t  
sequenceOf hom = execIxStateT (hom (istateM (fmap (\b -> (pure (), b)))))

mapAccumLOf :: (IxMonadState n, IxMonadLift (State acc) n) 
            => ATraversal (State acc) Unit n s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t) 
mapAccumLOf hom f acc0 s = swap (runState (execIxStateT (hom (istateM g)) s) acc0)
  where g a = do
          acc <- get
          let (acc', b) = f acc a
          put acc'
          return (pure (), b)

failover :: (Alternative f, IxMonadState n) => ATraversal Identity (Const Any) n s t a b -> (a -> b) -> s -> f t 
failover hom f s
  | any == Const (Any False) = empty
  | otherwise = pure t
  where (any, t) = runIxState (hom (istate (\a -> (Const (Any True), f a)))) s

ifailover :: (Alternative f, IxMonadState n, IxMonadReader i n) => ATraversal Identity (Const Any) n s t a b -> (i -> a -> b) -> s -> f t 
ifailover hom f s
  | any == Const (Any False) = empty
  | otherwise = pure t
  where (any, t) = runIxState (hom (iaskstate (\i a -> (Const (Any True), f i a)))) s

-- TODO: Optimize this using a monad that can terminate in the middle
taking :: ( IxMonadStateHoist m (StateT Int p) m' p
          , IxMonadStateHoist n' p n (StateT Int p)
          , Monoid1 f )
          => Int -> Optic' m f n s t a a -> Optic' m' f n' s t a a
taking n hom sm = 
  istateHoist g (hom (istateHoist f sm))
  where f q a = do
          i <- get
          put (i + 1)
          if i > n     
          then return (mempty1, a)
          else lift (q a)
        g q s = fmap fst (runStateT (q s) 1)

dropping :: ( IxMonadStateHoist m (StateT Int p) m' p
            , IxMonadStateHoist n' p n (StateT Int p)
            , Monoid1 f )
            => Int -> Optic' m f n s t a a -> Optic' m' f n' s t a a
dropping n hom sm = 
  istateHoist g (hom (istateHoist f sm))
  where f q a = do
          i <- get
          put (i + 1)
          if i > n     
          then lift (q a)
          else return (mempty1, a)
        g q s = fmap fst (runStateT (q s) 1)

mapAccumLM :: (Traversable t, Monad m) => (a -> b -> m (a, c)) -> a -> t b -> m (a, t c) 
mapAccumLM f a tb = fmap swap (runStateT (traverse g tb) a)
  where g b = do
          a <- get
          (a', c) <- lift (f a b)
          put a'
          return c

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)