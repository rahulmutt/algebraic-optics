-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Internal.Indexed
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Internal.Indexed where

import Control.Monad.Reader

class IxPointed m where
    ireturn :: a -> m i i a

class IxFunctor m where
    imap :: (a -> b) -> m i j a -> m i j b

class (IxFunctor m, IxPointed m) => IxApplicative m where
    iap :: m i j (a -> b) -> m j k a -> m i k b

class (IxApplicative m) => IxMonad m where
    ibind :: m i j a -> (a -> m j k b) -> m i k b

(>>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>>=) = ibind

infixl 1 >>>=

class (IxMonad m) => IxMonadReader r m where
    iask :: m j j r

class IxMonad m => IxMonadState m where
    iget :: m i i i
    iput :: j -> m i j ()

imodify :: (IxMonadState m) => (i -> j) -> m i j ()
imodify f = iget >>>= iput . f 

istate :: (IxMonadState m) => (s -> (a, t)) -> m s t a
istate f = iget >>>= (\s -> let (a, t) = f s in iput t >>>= (const (ireturn a)))

class (Monad m, IxMonad n) => IxMonadLift n m | n -> m where
    ilift :: m a -> n i i a

newtype IxState i j a = 
    IxState { runIxState :: i -> (a, j) }

instance IxPointed IxState where
    ireturn a = IxState $ \i -> (a, i)

instance IxFunctor IxState where
    imap f (IxState state) =
         IxState $ \i -> 
            let (a, j) = state i 
            in (f a, j)

instance IxApplicative IxState where
    iap (IxState stateAB) (IxState stateA) =
        IxState $ \i -> 
            let (ab, j) = stateAB i
                (a,  k) = stateA j
            in (ab a, k)

instance IxMonad IxState where
    ibind (IxState state) f =
        IxState $ \i -> 
            let (a, j) = state i
                (b, k) = runIxState (f a) j
            in (b, k)

instance IxMonadState IxState where
    iget = IxState $ \i -> (i, i)
    iput j = IxState $ \_ -> ((), j)

execIxState :: IxState s t a -> s -> t
execIxState ixs = snd . runIxState ixs

evalIxState :: IxState s t a -> s -> a
evalIxState ixs = fst . runIxState ixs

newtype IxStateT m i j a =
    IxStateT { runIxStateT :: i -> m (a, j) }

instance (Applicative f) => IxPointed (IxStateT f) where
    ireturn a = IxStateT $ \i -> pure (a, i)

instance (Functor f) => IxFunctor (IxStateT f) where
    imap f (IxStateT state) =
         IxStateT $ fmap (\(a, j) -> (f a, j)) . state

instance (Monad m) => IxApplicative (IxStateT m) where
    iap (IxStateT stateAB) (IxStateT stateA) =
        IxStateT $ \i -> do
            (ab, j) <- stateAB i
            (a,  k) <- stateA j
            return (ab a, k)

instance (Monad m) => IxMonad (IxStateT m) where
    ibind (IxStateT state) f =
        IxStateT $ \i -> do
            (a, j) <- state i
            (b, k) <- runIxStateT (f a) j
            return (b, k)

instance (MonadReader r m) => IxMonadReader r (IxStateT m) where
    iask = IxStateT $ \j -> ask >>= (\r -> return (r, j))

instance (Monad m) => IxMonadState (IxStateT m) where
    iget = IxStateT $ \i -> return (i, i)
    iput j = IxStateT $ \_ -> return ((), j)

instance (Monad m) => IxMonadLift (IxStateT m) m where
    ilift ma = IxStateT $ \i -> ma >>= (\a -> return (a, i))

execIxStateT :: (Functor m) => IxStateT m s t a -> s -> m t
execIxStateT ixs = fmap snd . runIxStateT ixs

evalIxStateT :: (Functor m) => IxStateT m s t a -> s -> m a
evalIxStateT ixs = fmap fst . runIxStateT ixs

data IxReturnT m i j a = 
    IxReturnT { runReturn  :: Maybe a
              , runReturnT :: m i j a }

noIxReturnT :: m i j a -> IxReturnT m i j a
noIxReturnT = IxReturnT Nothing

instance (IxPointed m) => IxPointed (IxReturnT m) where
    ireturn a = IxReturnT (Just a) (ireturn a)

instance (IxFunctor m) => IxFunctor (IxReturnT m) where
    imap f (IxReturnT ret m) = IxReturnT (fmap f ret) (imap f m)

instance (IxApplicative m) => IxApplicative (IxReturnT m) where
    iap (IxReturnT retab mab) (IxReturnT reta ma) =
        IxReturnT (retab <*> reta) (iap mab ma)

instance (IxMonad m) => IxMonad (IxReturnT m) where
    ibind (IxReturnT _ ma) f =
        noIxReturnT (ibind ma (runReturnT . f))

instance (IxMonadReader r m) => IxMonadReader r (IxReturnT m) where
    iask = noIxReturnT iask

instance (IxMonadState m) => IxMonadState (IxReturnT m) where
    iget = noIxReturnT iget
    iput j = noIxReturnT (iput j)

instance (IxMonadLift n m) => IxMonadLift (IxReturnT n) m where
    ilift ma = noIxReturnT (ilift ma)