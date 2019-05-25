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
import Control.Monad.State

type Nat f p g = forall x. g (p x) -> f (p x)

type Optic' m f n s t a b = forall i j. Optic m i f n j s t a b
type Optic m i f n j s t a b = Nat (m i s t) f (n j a b)

-- TODO Make this IxGet instead for type-safety
type Getter s a = forall m f n. (IxMonadState m, IxMonadLift n m) => Optic' m f (IxStateT n) s s a a
type IndexedGetter i s a = forall m f n. (IxMonadState m, IxMonadLift n m) => Optic' m f (IxReaderStateT i n) s s a a

-- TODO Make this IxGet instead for type-safety
type RelaxedGetter s a = forall m f n. IxMonadLift n m => Optic' m f (IxStateT n) s s a a
type RelaxedIndexedGetter i s a = forall m f n. IxMonadLift n m => Optic' m f (IxReaderStateT i n) s s a a

type AFold f n s a = AFoldM Identity f n s a
type AFoldM m f n s a = Optic' (IxStateT m) f n s s a a

type AGetter n s a = AGetterM Identity n s a
type AGetterM m n s a = AFoldM m Identity n s a

type ASetter n s t a b = ASetterM Identity n s t a b
type ASetterM m n s t a b =  Optic' (IxStateT m) Unit n s t a b

type AReview n s a = AReviewM Identity n s a
type AReviewM m n s a = Optic (IxWriterT (IxStateT m)) (m s) Unit n (m a) s s a a

type APrism' n s a = APrism n s s a a
type APrism n s t a b = forall f. (Monoid1 f) => APrismF f n s t a b

type APrismF' f n s a = APrismF f n s s a a
type APrismF f n s t a b = forall i. Optic (IxWriterT (IxStateT Identity)) (Identity t) f n i s t a b

type Prism' s a = Prism s s a a
type Prism s t a b = PrismM Identity s t a b

type PrismM' m s a = PrismM m s s a a
type PrismM m s t a b = forall im f i. (IxMonadState im, IxMonadWriter im, IxMonadLift m im, Monoid1 f) 
                       => Optic im (m t) f (IxWriterT (IxStateT m)) i s t a b

type Iso s t a b = forall m f n. (IxMonadState m, IxMonadLift n m) => Optic' m f (IxStateT n) s t a b

type Lens' s a = Lens s s a a
type Lens s t a b = forall m f n. (IxMonadState m, IxMonadLift n m) => Optic' m f (IxStateT n) s t a b

type IndexedLens' i s a = IndexedLens i s s a a
type IndexedLens i s t a b = forall m f n. (IxMonadState m, IxMonadLift n m) => Optic' m f (IxReaderStateT i n) s t a b

type LensM' m s t a b = LensM m s s a a
type LensM m s t a b = forall im f. (IxMonadState im, IxMonadLift m im) => Optic' im f (IxStateInstrumentT m) s t a b

type LensIO' s a = LensIO s s a a
type LensIO s t a b = forall m. (MonadIO m) => LensM m s t a b

type ATraversal m f n s t a b = Optic' (IxStateT m) f n s t a b

type Traversal' s a = Traversal s s a a
type Traversal s t a b = forall m f n. (IxMonadState m, IxMonadLift n m, Monoid1 f) => Optic' m f (IxStateT n) s t a b

type Traversal1' s a = Traversal1 s s a a
type Traversal1 s t a b = forall m f n. (IxMonadState m, IxMonadLift n m, Semigroup1 f) => Optic' m f (IxStateT n) s t a b

type IndexedTraversal' i s a = IndexedTraversal i s s a a
type IndexedTraversal i s t a b = forall m f n. (IxMonadState m, IxMonadLift n m, Monoid1 f) => Optic' m f (IxReaderStateT i n) s t a b

-- TODO You can do better than IxState
type Fold  s a = forall m f n. (IxMonadGet m, IxMonadLift n m, Monoid1 f)    => Optic' m f (IxStateT n) s s a a
type Fold1 s a = forall m f n. (IxMonadGet m, IxMonadLift n m, Semigroup1 f) => Optic' m f (IxStateT n) s s a a 

-- TODO You can do better than IxStateT
type IndexedFold  i s a = forall m f n. (IxMonadGet m, IxMonadLift n m, Monoid1 f) => Optic' m f (IxReaderStateT i n) s s a a
type IndexPreservingFold i s a = forall m f n. (IxMonadGet m, IxMonadLift n m, IxMonadReader i m, Monoid1 f) => Optic' m f (IxReaderStateT i n) s s a a
type IndexedFold1 i s a = forall m f n. (IxMonadGet m, IxMonadLift n m, Semigroup1 f) => Optic' m f (IxReaderStateT i n) s s a a

class Semigroup1 f where
    mappend1 :: f a -> f a -> f a

    default mappend1 :: Semigroup (f a) => f a -> f a -> f a
    mappend1 = (<>)

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
    => Semigroup1 Identity where
    mappend1 = error "Semigroup1: Identity"

instance Semigroup1 Endo

instance Semigroup1 First

instance (Semigroup s) => Semigroup1 (Const s)

class Semigroup1 f => Monoid1 f where
    mempty1 :: f a

    default mempty1  :: Monoid (f a) => f a
    mempty1 = mempty

instance (TypeError ('Text "The function expects a Lens, but you supplied a Prism or Traversal")) 
      => Monoid1 Identity where
    mempty1 = error "Monoid1: Identity"

instance Monoid1 Endo

instance Monoid1 First

instance Monoid m => Monoid1 (Const m)

newtype ReverseMonoid f a = ReverseMonoid { getReverseMonoid :: f a }

instance (Semigroup1 f) => Semigroup1 (ReverseMonoid f) where
    mappend1 (ReverseMonoid m1) (ReverseMonoid m2) = ReverseMonoid (m2 `mappend1` m1)

instance (Monoid1 f) => Monoid1 (ReverseMonoid f) where
    mempty1 = ReverseMonoid mempty1

newtype Unit a = Unit (Const () a)
  deriving (Semigroup, Monoid, Functor, Applicative, Semigroup1, Monoid1)

data ProductMonoid f g a = ProductMonoid { getProductFirst :: f a, getProductSecond :: g a }

instance (Semigroup1 f, Semigroup1 g) => Semigroup1 (ProductMonoid f g) where
    mappend1 (ProductMonoid f1 g1) (ProductMonoid f2 g2) = ProductMonoid (f1 `mappend1` f2) (g1 `mappend1` g2)

instance (Monoid1 f, Monoid1 g) => Monoid1 (ProductMonoid f g) where
    mempty1 = ProductMonoid mempty1 mempty1

-- Reverse State Monad

newtype ReverseState s a = ReverseState { runReverseState :: s -> (a, s) }

instance Functor (ReverseState s) where
    fmap f (ReverseState rsm) = ReverseState $ \s ->
        let (a, s') = rsm s
        in (f a, s')

instance Applicative (ReverseState s) where
    pure a = ReverseState $ \s -> (a, s)
    ReverseState rsmab <*> ReverseState rsma = ReverseState $ \s ->
        let (ab, s'')  = rsmab s'
            (a,  s')   = rsma s
        in (ab a, s'')

instance Monad (ReverseState s) where
    ReverseState rsm >>= f = ReverseState $ \s ->
        let (a, s'') = rsm s'
            (b, s')  = runReverseState (f a) s
        in (b, s'')

instance MonadFix (ReverseState s) where
    mfix f = ReverseState $ \s -> fix (\(~(a, _)) -> runReverseState (f a) s)

instance MonadState s (ReverseState s) where
    get = ReverseState $ \s -> (s, s)
    put s = ReverseState $ \_ -> ((), s)