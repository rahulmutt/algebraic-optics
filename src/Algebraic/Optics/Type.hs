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

type ALensM' m s t a b = ALensM m s s a a
type ALensM m s t a b = LensM m (IxStateInstrumentT m) s t a b

type AIndexedTraversal' i s a = AIndexedTraversal i s s a a
type AIndexedTraversal i s t a b = forall m f. (IxMonadState m, Monoid1 f) => Optic' m f (IxStateT (Reader i)) s t a b

type ATraversal' s a = ATraversal s s a a
type ATraversal s t a b = forall m f. (IxMonadState m, Monoid1 f) => Optic' m f IxState s t a b

type ALensIO' s a = ALensIO s s a a
type ALensIO s t a b = forall m. (MonadIO m) => ALensM m s t a b

class Monoid1 m where
    mempty1 :: m a
    mappend1 :: m a -> m a -> m a

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
    => Monoid1 Identity where
    mempty1 = undefined
    mappend1 = undefined

instance Monoid1 Endo where
    mempty1 = mempty
    mappend1 = mappend

instance Monoid1 First where
    mempty1 = mempty
    mappend1 = mappend

instance (Monoid m) => Monoid1 (Const m) where
    mempty1 = mempty
    mappend1 = mappend