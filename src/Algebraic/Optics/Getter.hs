-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Getter
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Getter where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Data.Functor.Identity

infixl 8 ^., ^.!, ^@., ^@.!

to :: (s -> a) -> AGetter s a
to f sm = igetsM (evalIxStateT sm . f)

ito :: (s -> (i, a)) -> AIndexedGetter i s a
ito f sm = igetsM (\s -> let (i, a) = f s in evalIxReaderStateT sm i a)

like :: a -> ARelaxedGetter s a
like a sm = ilift (evalIxStateT sm a)

ilike :: i -> a -> ARelaxedIndexedGetter i s a
ilike i a sm = ilift (evalIxReaderStateT sm i a)

(^.) :: (IxMonadState n) => s -> Getter Identity n s a -> a
(^.) t hom = runIdentity $ evalIxState (hom (imap pure iget)) t

(^.!) :: (IxMonadState n, Monad m) => s -> GetterM m Identity n s a -> m a
(^.!) t hom = fmap runIdentity $ evalIxStateT (hom (imap pure iget)) t

(^@.) :: (IxMonadState n, IxMonadReader i n) => s -> Getter Identity n s a -> (i, a)
(^@.) t hom = runIdentity $ evalIxState (hom n) t
  where n = iask >>>= (\i -> 
            istate (\a -> (pure (i, a), a)))

(^@.!) :: (IxMonadState n, IxMonadReader i n, Monad m) => s -> GetterM m Identity n s a -> m (i, a)
(^@.!) t hom = fmap runIdentity $ evalIxStateT (hom n) t
  where n = iask >>>= (\i -> 
            istate (\a -> (pure (i, a), a)))