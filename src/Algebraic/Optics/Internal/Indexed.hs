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
    ireturn :: a -> m i i a

class IxFunctor m where
    imap :: (a -> b) -> m i j a -> m i j b

class (IxFunctor m, IxPointed m) => IxApplicative m where
    iap :: m i j (a -> b) -> m j k a -> m i k b

class IxApplicative m => IxMonad m where
    ibind :: m i j a -> (a -> m j k b) -> m i k b

(>>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>>=) = ibind

infixl 1 >>>=

class IxMonad m => IxMonadReader r m | m -> r where
    iask :: m i i r

class IxMonad m => IxMonadGet m where
    iget :: m i i i

igets :: IxMonadGet m => (i -> r) -> m i i r
igets f = imap f iget

iwith :: (IxMonadReader r m, IxMonadGet m) => (r -> i -> t) -> m i i t
iwith f = iask >>>= igets . f

class IxMonadGet m => IxMonadState m where
    iput :: j -> m i j ()

imodify :: IxMonadState m => (i -> j) -> m i j ()
imodify f = iget >>>= iput . f 

istate :: IxMonadState m => (s -> (a, t)) -> m s t a
istate f = iget >>>= (\s -> let (a, t) = f s in iput t >>>= (const (ireturn a)))

iaskstate :: (IxMonadState m, IxMonadReader i m) => (i -> s -> (a, t)) -> m s t a
iaskstate f = iask >>>= istate . f

class IxMonadWriter w m where
    itell :: w -> m i i ()

class (Monad m, IxMonad n) => IxMonadLift m n | n -> m where
    ilift :: m a -> n i i a

igetsM :: (IxMonadGet m, IxMonadLift n m) => (i -> n r) -> m i i r
igetsM f = iget >>>= ilift . f

iwithM :: (IxMonadReader r m, IxMonadGet m, IxMonadLift n m) => (r -> i -> n t) -> m i i t
iwithM f = iask >>>= igetsM . f

imodifyM :: (IxMonadState m, IxMonadLift n m) => (i -> n j) -> m i j ()
imodifyM f = igetsM f >>>= iput

istateM :: (IxMonadState im, IxMonadLift m im) => (s -> m (a, t)) -> im s t a
istateM f = 
    iget >>>= (\s -> 
    ilift (f s) >>>= (\(a, t) -> 
    iput t >>>= (const (ireturn a))))

iaskstateM :: (IxMonadState im, IxMonadLift m im, IxMonadReader i im) => (i -> s -> m (a, t)) -> im s t a
iaskstateM f = iask >>>= istateM . f

class (IxMonadState m, IxMonadState n, IxMonadLift p m, IxMonadLift q n) =>
       IxMonadStateHoist m p n q | m q -> n p, n p -> m q, m n -> p q where
    istateHoist :: ((i -> p (a, j)) -> (i -> q (a, j))) -> m i j a -> n i j a

type IxState i j a = IxStateT Identity i j a

runIxState :: IxState s t a -> s -> (a, t)
runIxState m s = runIdentity (runIxStateT m s)

execIxState :: IxState s t a -> s -> t
execIxState ixs = snd . runIxState ixs

evalIxState :: IxState s t a -> s -> a
evalIxState ixs = fst . runIxState ixs

newtype IxStateT m i j a =
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

instance Monad m => IxMonadWriter b (IxStateT m) where
    itell _ = ireturn ()

instance (Monad m, Monad n) => IxMonadStateHoist (IxStateT m) m (IxStateT n) n where
    istateHoist hoist (IxStateT f) = IxStateT (hoist f)

execIxStateT :: Functor m => IxStateT m s t a -> s -> m t
execIxStateT ixs = fmap snd . runIxStateT ixs

evalIxStateT :: Functor m => IxStateT m s t a -> s -> m a
evalIxStateT ixs = fmap fst . runIxStateT ixs

newtype IxReaderStateT r m i j a =
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

instance Monad m => IxMonadWriter b (IxReaderStateT r m) where
    itell _ = ireturn ()

instance (Monad m, Monad n) => IxMonadStateHoist (IxReaderStateT r m) m (IxReaderStateT r n) n where
    istateHoist hoist (IxReaderStateT f) = IxReaderStateT (\r i -> hoist (f r) i)

runIxReaderStateT :: IxReaderStateT r m s t a -> r -> s -> m (a, t)
runIxReaderStateT = unIxReaderStateT

execIxReaderStateT :: Functor m => IxReaderStateT r m s t a -> r -> s -> m t
execIxReaderStateT ixs r = fmap snd . runIxReaderStateT ixs r

evalIxReaderStateT :: Functor m => IxReaderStateT r m s t a -> r -> s -> m a
evalIxReaderStateT ixs r = fmap fst . runIxReaderStateT ixs r

newtype IxStateInstrumentT m i j a =
    IxStateInstrumentT { runIxStateInstrumentT' :: i -> Bool -> m (a, j, Bool) }

runIxStateInstrumentT :: IxStateInstrumentT m i j a -> i ->  m (a, j, Bool)
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

instance Monad m => IxMonadWriter b (IxStateInstrumentT m) where
    itell _ = ireturn ()

instance (Monad m, Monad n) => IxMonadStateHoist (IxStateInstrumentT m) m (IxStateInstrumentT n) n where
    istateHoist hoist (IxStateInstrumentT f) =
        IxStateInstrumentT (\i b -> fmap (extend b) $ hoist (fmap discard . flip f b) i)
      where discard (x, y, _) = (x, y)
            extend  z (x, y)  = (x, y, z)

execIxStateInstrumentT :: Functor m => IxStateInstrumentT m s t a -> s -> m t
execIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (_,b,_) = b

evalIxStateInstrumentT :: Functor m => IxStateInstrumentT m s t a -> s -> m a
evalIxStateInstrumentT ixs s = fmap f (runIxStateInstrumentT ixs s)
  where f (a,_,_) = a

data IxWriterT w m i j a = IxWriterT (Maybe w) (m i j a)

noIxWriterT :: m i j a -> IxWriterT w m i j a
noIxWriterT = IxWriterT Nothing

runIxWriterT :: IxWriterT w m i j a -> (Maybe w, m i j a)
runIxWriterT (IxWriterT a b) = (a, b)

evalIxWriterT :: IxWriterT w m i j a -> m i j a
evalIxWriterT = snd . runIxWriterT

execIxWriterT :: IxWriterT w m i j a -> Maybe w
execIxWriterT = fst . runIxWriterT

instance IxPointed m => IxPointed (IxWriterT w m) where
    ireturn a = noIxWriterT (ireturn a)

instance IxFunctor m => IxFunctor (IxWriterT w m) where
    imap f (IxWriterT r m) = IxWriterT r (imap f m)

instance IxApplicative m => IxApplicative (IxWriterT w m) where
    iap (IxWriterT _ mab) (IxWriterT r ma) = IxWriterT r (iap mab ma)

instance IxMonad m => IxMonad (IxWriterT w m) where
    ibind (IxWriterT r ma) f = IxWriterT r (ibind ma (evalIxWriterT . f))

instance IxMonadReader r m => IxMonadReader r (IxWriterT w m) where
    iask = noIxWriterT iask

instance IxMonadGet m => IxMonadGet (IxWriterT w m) where
    iget = noIxWriterT iget

instance IxMonadState m => IxMonadState (IxWriterT w m) where
    iput j = noIxWriterT (iput j)

instance IxMonadLift m n => IxMonadLift m (IxWriterT w n) where
    ilift ma = noIxWriterT (ilift ma)

instance IxMonad m => IxMonadWriter w (IxWriterT w m) where
    itell w = IxWriterT (Just w) (ireturn ())

instance IxMonadStateHoist m p n q => IxMonadStateHoist (IxWriterT w m) p (IxWriterT w n) q where
    istateHoist hoist (IxWriterT w m) = IxWriterT w (istateHoist hoist m)

{-

newtype IxMonadicState m i j a = IxMonadicState { runIxMonadicState :: m i -> m (a, j) }

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
-}