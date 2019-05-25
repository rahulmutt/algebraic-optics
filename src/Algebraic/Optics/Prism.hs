-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Prism
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Prism where

import Algebraic.Optics.Type
import Algebraic.Optics.Getter
import Algebraic.Optics.Lens
import Algebraic.Optics.Internal.Indexed

import Unsafe.Coerce
import Data.Void
import Data.Maybe
import Data.Monoid
import Data.Functor.Const
import Data.Functor.Identity
import Data.Bifunctor
import Text.Read (readMaybe)

prism :: forall s t a b. (b -> t) -> (s -> Either t a) -> Prism s t a b 
prism f g = prismM (Identity . f) (Identity . g)

prismM :: forall m s t a b. (b -> m t) -> (s -> m (Either t a)) -> PrismM m s t a b 
prismM f g sm' =
    itell t >>>= (\_ ->
    istateM (\s -> do
        mta <- g s
        case mta of
            Left  t -> return (mempty1, t)
            Right a -> do
               (r, b) <- runIxStateT sm a 
               t      <- f b
               return (r, t)))
    where (mret, sm) = runIxWriterT sm'
          t = (unsafeCoerce (fromJust mret) :: m b) >>= f

prism' :: (b -> s) -> (s -> Maybe a) -> Prism s s a b 
prism' f g = prism f (\s -> maybe (Left s) Right $ g s)

withPrism :: (IxMonadState n, IxMonadWriter (Identity b) n) => APrism n s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r 
withPrism prism f = f (unsafeReview prism) (matching prism)

unsafeReview :: (IxMonadState n, IxMonadWriter (Identity b) n) => APrism n s t a b -> b -> t
unsafeReview prism b
  | Just s <- execIxWriterT (prism (imap (pure :: () -> Unit ()) 
                            (itell (Identity b) >>>= const (iput b))))
  = runIdentity s
  | otherwise = error "Bad unsafeReview"

clonePrism :: ARawPrism s t a b -> Prism s t a b 
clonePrism p = withPrism p prism

outside :: ARawPrism s t a b -> Lens (t -> r) (s -> r) (b -> r) (a -> r)
outside p = withPrism p $ \f g -> lens (\tr -> tr . f) (\tr ar s -> either tr ar (g s))

aside :: ARawPrism s t a b -> Prism (e, s) (e, t) (e, a) (e, b) 
aside p = withPrism p $ \f g -> prism (fmap f) (\(e, s) -> bimap (e,) (e,) (g s))

without :: ARawPrism s t a b -> ARawPrism u v c d -> Prism (Either s u) (Either t v) (Either a c) (Either b d) 
without p1 p2 = 
  withPrism p1 $ \f1 g1 ->
    withPrism p2 $ \f2 g2 ->
      prism (bimap f1 f2) (either (bimap Left Left . g1) (bimap Right Right . g2))

below :: (Traversable t) => ARawPrism' s a -> Prism' (t s) (t a)
below p = prism' (fmap (p #)) (either (const Nothing) Just . traverse (matching p))

isn't :: IxMonadState n => APrismF (Const Any) n s t a b -> s -> Bool
isn't hom = not . getAny . getConst . evalIxState (evalIxWriterT (hom n))
  where n = istate (const (Const (Any True), undefined))
        -- The use of undefined is safe since `b` isn't really used

matching :: IxMonadState n => APrismF First n s t a b -> s -> Either t a
matching hom s = 
    case runIxState (evalIxWriterT (hom n)) s of
        (First (Just a), _) -> Right a
        (_, t)              -> Left t
    where n = istate (\a -> (pure a, undefined))
          -- The use of undefined is safe since `b` isn't really used

_Left :: Prism (Either a c) (Either b c) a b
_Left = prism Left (either Right (Left . Right))

_Right :: Prism (Either c a) (Either c b) a b
_Right = prism Right (either (Left . Left) Right)

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just (maybe (Left Nothing) Right)

_Nothing :: Prism' (Maybe a) ()
_Nothing = prism' (const Nothing) (maybe (Just ()) (const Nothing))

_Void :: Prism s s a Void
_Void = prism absurd Left

_Show :: (Read a, Show a) => Prism' String a
_Show = prism' show readMaybe

only :: Eq a => a -> Prism' a ()
only a = prism' (const a) (\a0 -> if a0 == a then Just () else Nothing)

nearly :: a -> (a -> Bool) -> Prism' a () 
nearly a f = prism' (const a) (\a -> if f a then Just () else Nothing)

-- Reviews

unto :: (b -> t) -> Prism' t b
unto f = prism' f (const Nothing)

un :: (IxMonadState n) => AGetter n s a -> Prism' a s
un getter = unto (^. getter)

re :: AReview t b -> Getter b t
re rev = to (rev #)

(#) :: AReview s a -> a -> s
(#) hom a = runIdentity (hom #! a)

(#!) :: forall m s a. Monad m => AReviewM m s a -> a -> m s
(#!) hom a
  | Just ms <- execIxWriterT (hom (imap pure (itell n)))
  = ms
  | otherwise = error "Bad review!"
  where n :: m a
        n = return a

infixr 8 #, #!