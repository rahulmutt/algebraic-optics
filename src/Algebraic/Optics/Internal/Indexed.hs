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
    ireturn :: a -> m s i i a

class IxFunctor m where
    imap :: (a -> b) -> m s i j a -> m s i j b

class (IxFunctor m, IxPointed m) => IxApplicative m where
    iap :: m s i j (a -> b) -> m s j k a -> m s i k b

class (IxApplicative m) => IxMonad m where
    ibind :: m s i j a -> (a -> m s j k b) -> m s i k b

(>>>=) :: IxMonad m => m s i j a -> (a -> m s j k b) -> m s i k b
(>>>=) = ibind

infixl 1 >>>=

class (IxMonad m) => IxMonadReader r m where
    iask :: m s i i r

class IxMonad m => IxMonadState m where
    iget :: m s i i i
    iput :: j -> m s i j ()

imodify :: (IxMonadState m) => (i -> j) -> m s i j ()
imodify f = iget >>>= iput . f 

istate :: (IxMonadState m) => (s -> (a, t)) -> m w s t a
istate f = iget >>>= (\s -> let (a, t) = f s in iput t >>>= (const (ireturn a)))

class IxMonadWriter m where
    itell :: t -> m t i i ()

class (Monad m, IxMonad n) => IxMonadLift n m | n -> m where
    ilift :: m a -> n s i i a

newtype IxState s i j a = 
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

instance IxMonadWriter IxState where
    itell _ = ireturn ()

execIxState :: IxState w s t a -> s -> t
execIxState ixs = snd . runIxState ixs

evalIxState :: IxState w s t a -> s -> a
evalIxState ixs = fst . runIxState ixs

newtype IxStateT m s i j a =
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
            runIxStateT (f a) j

instance (MonadReader r m) => IxMonadReader r (IxStateT m) where
    iask = IxStateT $ \j -> ask >>= (\r -> return (r, j))

instance (Monad m) => IxMonadState (IxStateT m) where
    iget = IxStateT $ \i -> return (i, i)
    iput j = IxStateT $ \_ -> return ((), j)

instance (Monad m) => IxMonadLift (IxStateT m) m where
    ilift ma = IxStateT $ \i -> ma >>= (\a -> return (a, i))

instance (Monad m) => IxMonadWriter (IxStateT m) where
    itell _ = ireturn ()

execIxStateT :: (Functor m) => IxStateT m w s t a -> s -> m t
execIxStateT ixs = fmap snd . runIxStateT ixs

evalIxStateT :: (Functor m) => IxStateT m w s t a -> s -> m a
evalIxStateT ixs = fmap fst . runIxStateT ixs

newtype IxStateInstrumentT m s i j a =
    IxStateInstrumentT { runIxStateInstrumentT' :: i -> Bool -> m (a, j, Bool) }

runIxStateInstrumentT :: IxStateInstrumentT m s i j a -> i ->  m (a, j, Bool)
runIxStateInstrumentT m i = runIxStateInstrumentT' m i False

instance (Applicative f) => IxPointed (IxStateInstrumentT f) where
    ireturn a = IxStateInstrumentT $ \i b -> pure (a, i, b)

instance (Functor f) => IxFunctor (IxStateInstrumentT f) where
    imap f (IxStateInstrumentT state) =
         IxStateInstrumentT $ \i b -> fmap (\(a, j, c) -> (f a, j, c)) (state i b)

instance (Monad m) => IxApplicative (IxStateInstrumentT m) where
    iap (IxStateInstrumentT stateAB) (IxStateInstrumentT stateA) =
        IxStateInstrumentT $ \i b -> do
            (ab, j, c) <- stateAB i b
            (a,  k, d) <- stateA j c
            return (ab a, k, d)

instance (Monad m) => IxMonad (IxStateInstrumentT m) where
    ibind (IxStateInstrumentT state) f =
        IxStateInstrumentT $ \i b -> do
            (a, j, c) <- state i b
            runIxStateInstrumentT' (f a) j c

instance (MonadReader r m) => IxMonadReader r (IxStateInstrumentT m) where
    iask = IxStateInstrumentT $ \j b -> ask >>= (\r -> return (r, j, b))

instance (Monad m) => IxMonadState (IxStateInstrumentT m) where
    iget = IxStateInstrumentT $ \i b -> return (i, i, b)
    iput j = IxStateInstrumentT $ \_ _ -> return ((), j, True)

instance (Monad m) => IxMonadLift (IxStateInstrumentT m) m where
    ilift ma = IxStateInstrumentT $ \i b -> ma >>= (\a -> return (a, i, b))

instance (Monad m) => IxMonadWriter (IxStateInstrumentT m) where
    itell _ = ireturn ()

execIxStateInstrumentT :: (Functor m) => IxStateInstrumentT m w s t a -> s -> m t
execIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (_,b,_) = b

evalIxStateInstrumentT :: (Functor m) => IxStateInstrumentT m w s t a -> s -> m a
evalIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (a,_,_) = a

data IxReturnT m s i j a = 
    IxReturnT { getIxReturn :: Maybe s
              , getIxMonad  :: forall w. m w i j a }

noIxReturnT :: (forall w. m w i j a) -> IxReturnT m s i j a
noIxReturnT = IxReturnT Nothing

runIxReturnT :: IxReturnT m s i j a -> (Maybe s, m w i j a)
runIxReturnT ret = (getIxReturn ret, getIxMonad ret)

instance (IxPointed m) => IxPointed (IxReturnT m) where
    ireturn a = noIxReturnT (ireturn a)

instance (IxFunctor m) => IxFunctor (IxReturnT m) where
    imap f (IxReturnT r m) = IxReturnT r (imap f m)

instance (IxApplicative m) => IxApplicative (IxReturnT m) where
    iap (IxReturnT _ mab) (IxReturnT r ma) = IxReturnT r (iap mab ma)

instance (IxMonad m) => IxMonad (IxReturnT m) where
    ibind (IxReturnT r ma) f = IxReturnT r (ibind ma (getIxMonad . f))

instance (IxMonadReader r m) => IxMonadReader r (IxReturnT m) where
    iask = noIxReturnT iask

instance (IxMonadState m) => IxMonadState (IxReturnT m) where
    iget = noIxReturnT iget
    iput j = noIxReturnT (iput j)

instance (IxMonadLift n m) => IxMonadLift (IxReturnT n) m where
    ilift ma = noIxReturnT (ilift ma)

instance (IxMonad m) => IxMonadWriter (IxReturnT m) where
    itell t = IxReturnT (Just t) (ireturn ())