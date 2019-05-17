-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Fold
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Fold where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Control.Monad.Reader

import Data.Functor.Const

import Data.Int
import Data.Monoid

infixl 8 ^.., ^..!, ^?, ^?!, ^@.., ^@..!

(^..) :: (IxMonadGet n) => s -> Getter Endo n s a -> [a]
(^..) s hom = appEndo (evalIxState (hom (imap (Endo . (:)) iget)) s) []

(^..!) :: (IxMonadGet n, Monad m) => s -> GetterM Endo m n s a -> m [a]
(^..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom (imap (Endo . (:)) iget)) s)

(^?) :: (IxMonadGet n) => s -> Getter First n s a -> Maybe a
(^?) s hom = getFirst $ evalIxState (hom (imap pure iget)) s

(^?!) :: (IxMonadGet n, Monad m) => s -> GetterM First m n s a -> m (Maybe a)
(^?!) s hom = fmap getFirst $ evalIxStateT (hom (imap pure iget)) s

has :: (IxMonadGet n) => Getter (Const Any) n s a -> s -> Bool
has hom = getAny . getConst . evalIxState (hom (imap (const (Const (Any True))) iget))

hasn't :: (IxMonadGet n) => Getter (Const All) n s a -> s -> Bool
hasn't hom = getAll . getConst . evalIxState (hom (imap (const (Const (All False))) iget))

folding :: Foldable f => (s -> f a) -> AFold s a
folding f sm = 
   iget >>>= 
      ireturn 
    . foldr (\a b -> evalIxState sm a `mappend1` b) mempty1 
    . f

ifolding :: Foldable f => (s -> f (i, a)) -> AIndexedFold i s a
ifolding f sm = 
   iget >>>=
       ireturn 
     . foldr (\(i, a) b -> runReader (evalIxStateT sm a) i `mappend1` b) mempty1 
     . f
   
folded :: (Foldable f) => AIndexedFold Int (f a) a
folded = folded'

folded64 :: (Foldable f) => AIndexedFold Int64 (f a) a
folded64 = folded'

folded' :: (Foldable f, Integral i) => AIndexedFold i (f a) a
folded' sm = 
   iget >>>= 
     ireturn 
   . fst 
   . foldl (\(b, !n) a -> 
             ( b `mappend1` runReader (evalIxStateT sm a) n
             , n + 1))
           (mempty1, 0)

unfolded :: (b -> Maybe (a, b)) -> AFold b a
unfolded f sm = iget >>>= ireturn . go
   where go b 
           | Just (a, b') <- f b
           = evalIxState sm a `mappend1` go b'
           | otherwise
           = mempty1

iterated :: (a -> a) -> AFold1 a a
iterated f sm = iget >>>= ireturn . go
   where go a = evalIxState sm a `mappend1` go (f a)
   
filtered :: (a -> Bool) -> AFold a a
filtered f sm = 
   iget >>>= (\a ->
       if f a
       then ireturn (evalIxState sm a)
       else ireturn mempty1)

reversed :: (Monoid1 f, IxFunctor m, IxFunctor n) => Optic' m (ReverseMonoid f) n s t a b -> Optic' m f n s t a b
reversed revHom sm = imap getReverseMonoid (revHom (imap ReverseMonoid sm))

repeated :: AFold1 a a
repeated sm = iget >>>= ireturn . go
   where go a = evalIxState sm a `mappend1` go a

replicated :: Int -> AFold a a
replicated n sm = iget >>>= ireturn . go n
   where go  0 _ = mempty1
         go !n a = evalIxState sm a `mappend1` go (n - 1) a

cycled :: forall m f n s t a b. (Semigroup1 f, IxMonadState m) => Optic' m f n s t a b -> Optic' m f n s t a b
cycled hom sm = iget >>>= go
  where go s = hom sm >>>= (\gx -> 
               iput s >>>= (\_ ->
               go s >>>= (\hx ->
               ireturn (gx `mappend1` hx))))

-- Indexed

(^@..) :: (IxMonadState n, IxMonadReader i n) => s -> Getter Endo n s a -> [(i, a)]
(^@..) s hom = appEndo (evalIxState (hom n) s) []
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))

(^@..!) :: (IxMonadState n, IxMonadReader i n, Monad m) => s -> GetterM Endo m n s a -> m [(i, a)]
(^@..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom n) s)
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))