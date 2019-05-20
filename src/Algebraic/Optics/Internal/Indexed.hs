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
import Data.Functor.Identity

class IxPointed m where
    ireturn :: a -> m s i i a

class IxFunctor m where
    imap :: (a -> b) -> m s i j a -> m s i j b

class (IxFunctor m, IxPointed m) => IxApplicative m where
    iap :: m s i j (a -> b) -> m s j k a -> m s i k b

class IxApplicative m => IxMonad m where
    ibind :: m s i j a -> (a -> m s j k b) -> m s i k b

(>>>=) :: IxMonad m => m s i j a -> (a -> m s j k b) -> m s i k b
(>>>=) = ibind

infixl 1 >>>=

class IxMonad m => IxMonadReader r m | m -> r where
    iask :: m s i i r

class IxMonad m => IxMonadGet m where
    iget :: m s i i i

igets :: IxMonadGet m => (i -> r) -> m s i i r
igets f = imap f iget

iwith :: (IxMonadReader r m, IxMonadGet m) => (r -> i -> t) -> m s i i t
iwith f = iask >>>= igets . f

class IxMonadGet m => IxMonadState m where
    iput :: j -> m s i j ()

imodify :: IxMonadState m => (i -> j) -> m s i j ()
imodify f = iget >>>= iput . f 

istate :: IxMonadState m => (s -> (a, t)) -> m w s t a
istate f = iget >>>= (\s -> let (a, t) = f s in iput t >>>= (const (ireturn a)))

class IxMonadWriter m where
    itell :: t -> m t i i ()

class (Monad m, IxMonad n) => IxMonadLift m n | n -> m where
    ilift :: m a -> n s i i a

igetsM :: (IxMonadGet m, IxMonadLift n m) => (i -> n r) -> m s i i r
igetsM f = iget >>>= ilift . f

iwithM :: (IxMonadReader r m, IxMonadGet m, IxMonadLift n m) => (r -> i -> n t) -> m s i i t
iwithM f = iask >>>= igetsM . f

imodifyM :: (IxMonadState m, IxMonadLift n m) => (i -> n j) -> m s i j ()
imodifyM f = igetsM f >>>= iput

istateM :: (IxMonadState im, IxMonadLift m im) => (s -> m (a, t)) -> im w s t a
istateM f = 
    iget >>>= (\s -> 
    ilift (f s) >>>= (\(a, t) -> 
    iput t >>>= (const (ireturn a))))

newtype IxState s i j a = IxState { unIxState :: IxStateT Identity s i j a }
  deriving (IxPointed, IxFunctor, IxApplicative, IxMonad, IxMonadGet, IxMonadState, IxMonadLift Identity, IxMonadWriter)

runIxState :: IxState w s t a -> s -> (a, t)
runIxState m s = runIdentity (runIxStateT (unIxState m) s)

execIxState :: IxState w s t a -> s -> t
execIxState ixs = snd . runIxState ixs

evalIxState :: IxState w s t a -> s -> a
evalIxState ixs = fst . runIxState ixs

newtype IxStateT m s i j a =
    IxStateT { runIxStateT :: i -> m (a, j) }

instance Applicative f => IxPointed (IxStateT f) where
    ireturn a = IxStateT $ \i -> pure (a, i)

instance Functor f => IxFunctor (IxStateT f) where
    imap f (IxStateT state) =
         IxStateT $ fmap (\(a, j) -> (f a, j)) . state

instance Monad m => IxApplicative (IxStateT m) where
    iap (IxStateT stateAB) (IxStateT stateA) =
        IxStateT $ \i -> do
            (ab, j) <- stateAB i
            (a,  k) <- stateA j
            return (ab a, k)

instance Monad m => IxMonad (IxStateT m) where
    ibind (IxStateT state) f =
        IxStateT $ \i -> do
            (a, j) <- state i
            runIxStateT (f a) j

instance MonadReader r m => IxMonadReader r (IxStateT m) where
    iask = IxStateT $ \j -> ask >>= (\r -> return (r, j))

instance Monad m => IxMonadGet (IxStateT m) where
    iget = IxStateT $ \i -> return (i, i)

instance Monad m => IxMonadState (IxStateT m) where
    iput j = IxStateT $ \_ -> return ((), j)

instance Monad m => IxMonadLift m (IxStateT m) where
    ilift ma = IxStateT $ \i -> ma >>= (\a -> return (a, i))

instance Monad m => IxMonadWriter (IxStateT m) where
    itell _ = ireturn ()

execIxStateT :: Functor m => IxStateT m w s t a -> s -> m t
execIxStateT ixs = fmap snd . runIxStateT ixs

evalIxStateT :: Functor m => IxStateT m w s t a -> s -> m a
evalIxStateT ixs = fmap fst . runIxStateT ixs

newtype IxReaderStateT r m s i j a =
    IxReaderStateT { unIxReaderStateT :: r -> i -> m (a, j) }

instance Applicative f => IxPointed (IxReaderStateT r f) where
    ireturn a = IxReaderStateT $ \_ i -> pure (a, i)

instance Functor f => IxFunctor (IxReaderStateT r f) where
    imap f (IxReaderStateT state) =
         IxReaderStateT $ \r i -> fmap (\(a, j) -> (f a, j)) (state r i)

instance Monad m => IxApplicative (IxReaderStateT r m) where
    iap (IxReaderStateT stateAB) (IxReaderStateT stateA) =
        IxReaderStateT $ \r i -> do
            (ab, j) <- stateAB r i
            (a,  k) <- stateA  r j
            return (ab a, k)

instance Monad m => IxMonad (IxReaderStateT r m) where
    ibind (IxReaderStateT state) f =
        IxReaderStateT $ \r i -> do
            (a, j) <- state r i
            unIxReaderStateT (f a) r j

instance Monad m => IxMonadReader r (IxReaderStateT r m) where
    iask = IxReaderStateT $ \r j -> return (r, j)

instance Monad m => IxMonadGet (IxReaderStateT r m) where
    iget = IxReaderStateT $ \_ i -> return (i, i)

instance Monad m => IxMonadState (IxReaderStateT r m) where
    iput j = IxReaderStateT $ \_ _ -> return ((), j)

instance Monad m => IxMonadLift m (IxReaderStateT r m) where
    ilift ma = IxReaderStateT $ \_ i -> ma >>= (\a -> return (a, i))

instance Monad m => IxMonadWriter (IxReaderStateT r m) where
    itell _ = ireturn ()

runIxReaderStateT :: IxReaderStateT r m w s t a -> r -> s -> m (a, t)
runIxReaderStateT = unIxReaderStateT

execIxReaderStateT :: Functor m => IxReaderStateT r m w s t a -> r -> s -> m t
execIxReaderStateT ixs r = fmap snd . runIxReaderStateT ixs r

evalIxReaderStateT :: Functor m => IxReaderStateT r m w s t a -> r -> s -> m a
evalIxReaderStateT ixs r = fmap fst . runIxReaderStateT ixs r

newtype IxStateInstrumentT m s i j a =
    IxStateInstrumentT { runIxStateInstrumentT' :: i -> Bool -> m (a, j, Bool) }

runIxStateInstrumentT :: IxStateInstrumentT m s i j a -> i ->  m (a, j, Bool)
runIxStateInstrumentT m i = runIxStateInstrumentT' m i False

instance Applicative f => IxPointed (IxStateInstrumentT f) where
    ireturn a = IxStateInstrumentT $ \i b -> pure (a, i, b)

instance Functor f => IxFunctor (IxStateInstrumentT f) where
    imap f (IxStateInstrumentT state) =
         IxStateInstrumentT $ \i b -> fmap (\(a, j, c) -> (f a, j, c)) (state i b)

instance Monad m => IxApplicative (IxStateInstrumentT m) where
    iap (IxStateInstrumentT stateAB) (IxStateInstrumentT stateA) =
        IxStateInstrumentT $ \i b -> do
            (ab, j, c) <- stateAB i b
            (a,  k, d) <- stateA j c
            return (ab a, k, d)

instance Monad m => IxMonad (IxStateInstrumentT m) where
    ibind (IxStateInstrumentT state) f =
        IxStateInstrumentT $ \i b -> do
            (a, j, c) <- state i b
            runIxStateInstrumentT' (f a) j c

instance MonadReader r m => IxMonadReader r (IxStateInstrumentT m) where
    iask = IxStateInstrumentT $ \j b -> ask >>= (\r -> return (r, j, b))

instance Monad m => IxMonadGet (IxStateInstrumentT m) where
    iget = IxStateInstrumentT $ \i b -> return (i, i, b)

instance Monad m => IxMonadState (IxStateInstrumentT m) where
    iput j = IxStateInstrumentT $ \_ _ -> return ((), j, True)

instance Monad m => IxMonadLift m (IxStateInstrumentT m) where
    ilift ma = IxStateInstrumentT $ \i b -> ma >>= (\a -> return (a, i, b))

instance Monad m => IxMonadWriter (IxStateInstrumentT m) where
    itell _ = ireturn ()

execIxStateInstrumentT :: Functor m => IxStateInstrumentT m w s t a -> s -> m t
execIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (_,b,_) = b

evalIxStateInstrumentT :: Functor m => IxStateInstrumentT m w s t a -> s -> m a
evalIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (a,_,_) = a

data IxWriterT m s i j a = 
    IxWriterT { getIxReturn :: Maybe s
              , getIxMonad  :: forall w. m w i j a }

noIxWriterT :: (forall w. m w i j a) -> IxWriterT m s i j a
noIxWriterT = IxWriterT Nothing

runIxWriterT :: IxWriterT m s i j a -> (Maybe s, m w i j a)
runIxWriterT ret = (getIxReturn ret, getIxMonad ret)

instance IxPointed m => IxPointed (IxWriterT m) where
    ireturn a = noIxWriterT (ireturn a)

instance IxFunctor m => IxFunctor (IxWriterT m) where
    imap f (IxWriterT r m) = IxWriterT r (imap f m)

instance IxApplicative m => IxApplicative (IxWriterT m) where
    iap (IxWriterT _ mab) (IxWriterT r ma) = IxWriterT r (iap mab ma)

instance IxMonad m => IxMonad (IxWriterT m) where
    ibind (IxWriterT r ma) f = IxWriterT r (ibind ma (getIxMonad . f))

instance IxMonadReader r m => IxMonadReader r (IxWriterT m) where
    iask = noIxWriterT iask

instance IxMonadGet m => IxMonadGet (IxWriterT m) where
    iget = noIxWriterT iget

instance IxMonadState m => IxMonadState (IxWriterT m) where
    iput j = noIxWriterT (iput j)

instance IxMonadLift m n => IxMonadLift m (IxWriterT n) where
    ilift ma = noIxWriterT (ilift ma)

instance IxMonad m => IxMonadWriter (IxWriterT m) where
    itell t = IxWriterT (Just t) (ireturn ())

newtype IxMonadicState m s i j a = IxMonadicState { runIxMonadicState :: m i -> m (a, j) }

pair :: (Applicative f) => f a -> f b -> f (a, b)
pair fa fb = (,) <$> fa <*> fb

instance (Applicative f) => IxPointed (IxMonadicState f) where
    ireturn a = IxMonadicState $ \mi -> pair (pure a) mi

instance (Applicative f) => IxFunctor (IxMonadicState f) where
    imap f (IxMonadicState state) =
         IxMonadicState $ \mi -> 
            let maj = state mi 
                ma = fmap fst maj
                mj = fmap snd maj
            in pair (fmap f ma) mj

instance (Applicative f) => IxApplicative (IxMonadicState f) where
    iap (IxMonadicState stateAB) (IxMonadicState stateA) =
        IxMonadicState $ \mi -> 
            let mabj = stateAB mi
                mab = fmap fst mabj
                mj  = fmap snd mabj
                mak = stateA mj
                ma = fmap fst mak
                mk = fmap snd mak
            in pair (mab <*> ma) mk

instance (Monad m) => IxMonad (IxMonadicState m) where
    ibind (IxMonadicState state) f =
        IxMonadicState $ \mi -> do
            let maj = state mi
                ma = fmap fst maj
                mj = fmap snd maj
            a <- ma 
            let mbk = runIxMonadicState (f a) mj
                mb = fmap fst mbk
                mk = fmap snd mbk
            pair mb mk

instance (Monad f) => IxMonadGet (IxMonadicState f) where
    iget = IxMonadicState $ \mi -> pair mi mi

instance (Monad f) => IxMonadState (IxMonadicState f) where
    iput j = IxMonadicState $ \_ -> pure ((), j)

instance (Applicative f) => IxMonadWriter (IxMonadicState f) where
    itell _ = ireturn ()