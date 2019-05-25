-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Setter
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Setter where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Data.Functor.Identity

infixr 4 .~, .~!, %~, %~!

(.~) :: (IxMonadState n) => ASetter n s t a b -> b -> s -> t
(.~) hom b s = runIdentity ((.~!) hom b s)

(.~!) :: (IxMonadState n, Monad m) => ASetterM m n s t a b -> b -> s -> m t
(.~!) hom b = execIxStateT (hom (imap pure (iput b)))

(%~) :: (IxMonadState n) => ASetter n s t a b -> (a -> b) -> s -> t
(%~) hom f s = runIdentity ((%~!) hom f s)

(%~!) :: (IxMonadState n, Monad m) => ASetterM m n s t a b -> (a -> b) -> s -> m t
(%~!) hom f = execIxStateT (hom (imap pure (imodify f)))

(.@~) :: (IxMonadState n, IxMonadReader i n) => ASetter n s t a b -> (i -> b) -> s -> t
(.@~) hom f s = runIdentity ((.@~!) hom f s)

(.@~!) :: (IxMonadState n, IxMonadReader i n, Monad m) => ASetterM m n s t a b -> (i -> b) -> s -> m t
(.@~!) hom f = execIxStateT (hom n)
  where n = iaskstate (\i _ -> (pure (), f i))

(%@~) :: (IxMonadState n, IxMonadReader i n) => ASetter n s t a b -> (i -> a -> b) -> s -> t
(%@~) hom f s = runIdentity ((%@~!) hom f s)

(%@~!) :: (IxMonadState n, IxMonadReader i n, Monad m) => ASetterM m n s t a b -> (i -> a -> b) -> s -> m t
(%@~!) hom f = execIxStateT (hom n)
  where n = iaskstate (\i a -> (pure (), f i a))