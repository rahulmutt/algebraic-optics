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

import Data.Monoid

infixl 8 ^.., ^..!, ^?, ^?!, ^@.., ^@..!

(^..) :: (IxMonadState n) => s -> Getter Endo n s a -> [a]
(^..) s hom = appEndo (evalIxState (hom (imap (Endo . (:)) iget)) s) []

(^..!) :: (IxMonadState n, Monad m) => s -> GetterM Endo m n s a -> m [a]
(^..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom (imap (Endo . (:)) iget)) s)

(^?) :: (IxMonadState n) => s -> Getter First n s a -> Maybe a
(^?) s hom = getFirst $ evalIxState (hom (imap pure iget)) s

(^?!) :: (IxMonadState n, Monad m) => s -> GetterM First m n s a -> m (Maybe a)
(^?!) s hom = fmap getFirst $ evalIxStateT (hom (imap pure iget)) s

(^@..) :: (IxMonadState n, IxMonadReader i n) => s -> Getter Endo n s a -> [(i, a)]
(^@..) s hom = appEndo (evalIxState (hom n) s) []
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))

(^@..!) :: (IxMonadState n, IxMonadReader i n, Monad m) => s -> GetterM Endo m n s a -> m [(i, a)]
(^@..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom n) s)
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))
