-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
module Algebraic.Optics where

import Control.Arrow

import Control.Monad.Reader
import Data.IORef
import Data.Int
import Data.Monoid
import Data.Functor.Identity
import Data.Traversable
import Algebraic.Optics.Equality
import Algebraic.Optics.Internal.Monoid1
import Algebraic.Optics.Internal.Indexed

infixr 4 .~, .~!, %~, %~!
infixl 8 ^., ^.!, ^.., ^..!, ^?, ^?!, ^@.., ^@..!

-- Types

type Nat f g h = forall x. g (h x) -> f (h x)

type Getter f n s a = forall m. (IxMonadState m) => Nat (m s s) (n a a) f
type GetterM f m n s a = forall im. (IxMonadState im, IxMonadLift im m) => Nat (im s s) (n a a) f

type Setter n s t a b = forall m. (IxMonadState m) => Nat (m s t) (n a b) First
type SetterM m n s t a b = forall im. (IxMonadState im, IxMonadLift im m) => Nat (im s t) (n a b) First

type Prism' n s a = Prism n s s a a
type Prism n s t a b = forall m f. (IxMonadState m, Monoid1 f) => Nat (m s t) (n a b) f

type APrism' s a = APrism s s a a
type APrism s t a b = forall m f. (IxMonadState m, Monoid1 f) => Nat (m s t) (IxState a b) f

type Lens n s t a b = forall m f. (IxMonadState m) => Nat (m s t) (n a b) f
type LensM m n s t a b = forall im f. (IxMonadState im, IxMonadLift im m) => Nat (im s t) (n a b) f

type ALens' s a = ALens s s a a
type ALens s t a b = forall m f. (IxMonadState m) => Nat (m s t) (IxState a b) f

type ALensM' m s t a b = ALensM m s s a a
type ALensM m s t a b = LensM m (IxStateT m) s t a b

type AIndexedTraversal' i s a = AIndexedTraversal i s s a a
type AIndexedTraversal i s t a b = forall m f. (IxMonadState m, Monoid1 f) => Nat (m s t) ((IxStateT (Reader i)) a b) f

type ATraversal' s a = ATraversal s s a a
type ATraversal s t a b = forall m f. (IxMonadState m, Monoid1 f) => Nat (m s t) (IxState a b) f

type ALensIO' s a = ALensIO s s a a
type ALensIO s t a b = forall m. (MonadIO m) => ALensM m s t a b

-- Combinators

(.~) :: (IxMonadState n) => Setter n s t a b -> b -> s -> t
(.~) hom b = execIxState (hom (imap pure (iput b)))

(.~!) :: (IxMonadState n, Monad m) => SetterM m n s t a b -> b -> s -> m t
(.~!) hom b = execIxStateT (hom (imap pure (iput b)))

(%~) :: (IxMonadState n) => Setter n s t a b -> (a -> b) -> s -> t
(%~) hom f = execIxState (hom (imap pure (imodify f)))

(%~!) :: (IxMonadState n, Monad m) => SetterM m n s t a b -> (a -> b) -> s -> m t
(%~!) hom f = execIxStateT (hom (imap pure (imodify f)))

(^.) :: (IxMonadState n) => s -> Getter Identity n s a -> a
(^.) t hom = runIdentity $ evalIxState (hom (imap pure iget)) t

(^.!) :: (IxMonadState n, Monad m) => s -> GetterM Identity m n s a -> m a
(^.!) t hom = fmap runIdentity $ evalIxStateT (hom (imap pure iget)) t

(^..) :: (IxMonadState n) => s -> Getter Endo n s a -> [a]
(^..) s hom = appEndo (evalIxState (hom (imap (Endo . (:)) iget)) s) []

(^..!) :: (IxMonadState n, Monad m) => s -> GetterM Endo m n s a -> m [a]
(^..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom (imap (Endo . (:)) iget)) s)

(^@..) :: (IxMonadState n, IxMonadReader i n) => s -> Getter Endo n s a -> [(i, a)]
(^@..) s hom = appEndo (evalIxState (hom n) s) []
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))

(^@..!) :: (IxMonadState n, IxMonadReader i n, Monad m) => s -> GetterM Endo m n s a -> m [(i, a)]
(^@..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom n) s)
   where n = iask >>>= (\i ->
             istate (\a -> (Endo ((i, a) :), a)))

(^?) :: (IxMonadState n) => s -> Getter First n s a -> Maybe a
(^?) s hom = getFirst $ evalIxState (hom (imap pure iget)) s

(^?!) :: (IxMonadState n, Monad m) => s -> GetterM First m n s a -> m (Maybe a)
(^?!) s hom = fmap getFirst $ evalIxStateT (hom (imap pure iget)) s

(^@.) :: (IxMonadState n, IxMonadReader i n) => s -> Getter Identity n s a -> (i, a)
(^@.) t hom = runIdentity $ evalIxState (hom n) t
  where n = iask >>>= (\i -> 
            istate (\a -> (pure (i, a), a)))

(^@.!) :: (IxMonadState n, IxMonadReader i n, Monad m) => s -> GetterM Identity m n s a -> m (i, a)
(^@.!) t hom = fmap runIdentity $ evalIxStateT (hom n) t
  where n = iask >>>= (\i -> 
            istate (\a -> (pure (i, a), a)))

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

prism :: (b -> t) -> (s -> Either t a) -> APrism s t a b 
prism f g sm = istate (\s -> 
  case g s of
    Left  t -> (mempty1, t)
    Right a -> let (r, b) = runIxState sm a in (r, f b))

prism' :: (b -> s) -> (s -> Maybe a) -> APrism s s a b 
prism' f g = prism f (\s -> maybe (Left s) Right $ g s)

_Just :: APrism (Maybe a) (Maybe b) a b
_Just = prism Just (maybe (Left Nothing) Right)

_Nothing :: APrism' (Maybe a) ()
_Nothing = prism' (const Nothing) (maybe (Just ()) (const Nothing))


fromVL :: (forall f. (Functor f) => (a -> f b) -> (s -> f t)) -> ALens s t a b
fromVL lens sm = istate (lens (runIxState sm))

-- Creating Lens

lens :: (s -> a) -> (s -> b -> t) -> ALens s t a b
lens getter setter sm = istate (\s -> second (setter s) (runIxState sm (getter s)))

mlens :: forall m s t a b. HasEquality s t a b => (s -> m a) -> (s -> a -> a -> m s) -> (s -> b -> m t) -> ALensM m s t a b
mlens getter msetter psetter sm = 
    iget >>>= (\s -> 
    ilift (getter s) >>>= (\a ->
    ilift (runIxStateT sm a) >>>= (\(r, b) ->
    case eq of
        Just Equality -> 
            ilift (msetter s a b) >>>= (\t ->
            iput t >>>= (\_ ->
            ireturn r))
        Nothing -> 
            ilift (psetter s b) >>>= (\t ->
            iput t >>>= (\_ ->
            ireturn r)))))
    where eq :: Maybe (Equality s t a b)
          eq = hasEquality

mlens' :: (s -> m a) -> (s -> a -> b -> m t) -> ALensM m s t a b
mlens' getter setter sm = 
    iget >>>= (\s -> 
    ilift (getter s) >>>= (\a ->
    ilift (runIxStateT sm a) >>>= (\(r, b) ->
    ilift (setter s a b) >>>= (\t ->
    iput t >>>= (\_ ->
    ireturn r)))))

mrefLens :: (a -> a -> Bool) -> (s -> IORef a) -> ALensIO' s a
mrefLens equals f = mlens' getter setter
   where getter s = liftIO (readIORef (f s))
         setter s a b = do
            when (not (equals a b)) $
              liftIO (writeIORef (f s) b)
            return s

mrefLensEq :: Eq a => (s -> IORef a) -> ALensIO' s a
mrefLensEq = mrefLens (==)

mrefLensNoEq :: (s -> IORef a) -> ALensIO' s a
mrefLensNoEq = mrefLens (\_ _ -> False)

prefLens :: HasEquality s t a b => (a -> a -> Bool) -> (s -> IORef a) -> (s -> IORef b -> t) -> ALensIO s t a b
prefLens equals f g = mlens getter msetter psetter
   where getter s = liftIO (readIORef (f s))
         msetter s a b = do
            when (not (equals a b)) $
              liftIO (writeIORef (f s) b)
            return s
         psetter s b = do
            ref <- liftIO (newIORef b)
            return (g s ref)

prefLensEq :: (HasEquality s t a b, Eq a) => (s -> IORef a) -> (s -> IORef b -> t) -> ALensIO s t a b
prefLensEq = prefLens (==)

prefLensNoEq :: HasEquality s t a b => (s -> IORef a) -> (s -> IORef b -> t) -> ALensIO s t a b
prefLensNoEq = prefLens (\_ _ -> False)