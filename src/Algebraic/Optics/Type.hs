-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Type
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Type where

import GHC.TypeLits hiding (Nat)
import Data.Functor.Identity
import Data.Monoid
import Data.Functor.Const
import Algebraic.Optics.Internal.Indexed
import Control.Monad.Reader

type Nat f p g = forall x. g (p x) -> f (p x)

type Optic' m f n s t a b = forall i j. Optic m i f n j s t a b
type Optic m i f n j s t a b = Nat (m i s t) f (n j a b)

type Getter f n s a = forall m. (IxMonadState m) => Optic' m f n s s a a
type GetterM f m n s a = forall im. (IxMonadState im, IxMonadLift im m) => Optic' im f n s s a a

type Setter n s t a b = forall m. (IxMonadState m) => Optic' m First n s t a b
type SetterM m n s t a b = forall im. (IxMonadState im, IxMonadLift im m) => Optic' im First n s t a b

type AReview n s a = forall m. (IxMonadState m, IxMonadWriter m) => Optic m s First n a s s a a
type AReviewM m n s a = forall im. (IxMonadState im, IxMonadWriter im, IxMonadLift im m) => Optic im (m s) First n (m a) s s a a

type APrism' s a = APrism s s a a
type APrism s t a b = forall m f i. (IxMonadState m, IxMonadWriter m, Monoid1 f) => Optic m t f (IxWriterT IxState) i s t a b

type APrismM' m s a = APrismM m s s a a
type APrismM m s t a b = forall im f i. (IxMonadState im, IxMonadWriter im, IxMonadLift im m, Monoid1 f) 
                       => Optic im (m t) f (IxWriterT (IxStateT m)) (m i) s t a b

type Lens n s t a b = forall m f. (IxMonadState m) => Optic' m f n s t a b
type LensM m n s t a b = forall im f. (IxMonadState im, IxMonadLift im m) => Optic' im f n s t a b

type ALens' s a = ALens s s a a
type ALens s t a b = forall m f. (IxMonadState m) => Optic' m f IxState s t a b
type ALensF f s t a b = forall m. (IxMonadState m) => Optic' m f IxState s t a b

type AIndexedLens' i s a = AIndexedLens i s s a a
type AIndexedLens i s t a b = forall m f. (IxMonadState m) => Optic' m f (IxStateT (Reader i)) s t a b

type ALensM' m s t a b = ALensM m s s a a
type ALensM m s t a b = LensM m (IxStateInstrumentT m) s t a b

type ALensIO' s a = ALensIO s s a a
type ALensIO s t a b = forall m. (MonadIO m) => ALensM m s t a b

type ATraversal' s a = ATraversal s s a a
type ATraversal s t a b = forall m f. (IxMonadState m, Monoid1 f) => Optic' m f IxState s t a b

type ATraversal1' s a = ATraversal1 s s a a
type ATraversal1 s t a b = forall m f. (IxMonadState m, Semigroup1 f) => Optic' m f IxState s t a b

type AIndexedTraversal' i s a = AIndexedTraversal i s s a a
type AIndexedTraversal i s t a b = forall m f. (IxMonadState m, Monoid1 f) => Optic' m f (IxStateT (Reader i)) s t a b

-- TODO You can do better than IxState
type AFold  s a = forall m f. (IxMonadGet m, Monoid1 f)    => Optic' m f IxState s s a a
type AFold1 s a = forall m f. (IxMonadGet m, Semigroup1 f) => Optic' m f IxState s s a a 

-- TODO You can do better than IxStateT
type AIndexedFold  i s a = forall m f. (IxMonadGet m, Monoid1 f)    => Optic' m f (IxStateT (Reader i)) s s a a
type AIndexedFold1 i s a = forall m f. (IxMonadGet m, Semigroup1 f) => Optic' m f (IxStateT (Reader i)) s s a a

class Semigroup1 f where
    mappend1 :: f a -> f a -> f a

    default mappend1 :: Semigroup (f a) => f a -> f a -> f a
    mappend1 = (<>)

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
    => Semigroup1 Identity where
    mappend1 = undefined

instance Semigroup1 Endo

instance Semigroup1 First

instance (Semigroup s) => Semigroup1 (Const s)

class Semigroup1 f => Monoid1 f where
    mempty1 :: f a

    default mempty1  :: Monoid (f a) => f a
    mempty1 = mempty

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
      => Monoid1 Identity where
    mempty1 = undefined

instance Monoid1 Endo

instance Monoid1 First

instance Monoid m => Monoid1 (Const m)

newtype ReverseMonoid f a = ReverseMonoid { getReverseMonoid :: f a }

instance (Semigroup1 f) => Semigroup1 (ReverseMonoid f) where
    mappend1 (ReverseMonoid m1) (ReverseMonoid m2) = ReverseMonoid (m2 `mappend1` m1)

instance (Monoid1 f) => Monoid1 (ReverseMonoid f) where
    mempty1 = ReverseMonoid mempty1