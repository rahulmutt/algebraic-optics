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
import Algebraic.Optics.Internal.Indexed

import Unsafe.Coerce
import Data.Maybe
import Data.Monoid
import Data.Functor.Const
import Data.Functor.Identity

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

-- TODO: Generlize this to s t a b 
withPrism :: (IxMonadGet n, IxMonadWriter n) => APrism n s t a a -> ((a -> t) -> (s -> Either t a) -> r) -> r 
withPrism prism f = f (runIdentity . bt . Identity) (matching prism)
  where bt b 
          | Just s <- execIxWriterT (prism (imap (pure :: () -> Unit ()) (itell b))) = s
          | otherwise = error "Bad review"

_Left :: Prism (Either a c) (Either b c) a b
_Left = prism Left (either Right (Left . Right))

_Right :: Prism (Either c a) (Either c b) a b
_Right = prism Right (either (Left . Left) Right)

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just (maybe (Left Nothing) Right)

_Nothing :: Prism' (Maybe a) ()
_Nothing = prism' (const Nothing) (maybe (Just ()) (const Nothing))

below :: (IxMonadWriter n, IxMonadState n, Traversable t) => APrism' n s a -> Prism' (t s) (t a)
below p = prism' (fmap (p #)) (either (const Nothing) Just . traverse (matching p))

-- TODO: Generlize this to s t a b 
isn't :: IxMonad n => APrismF (Const Any) n s t a a -> s -> Bool
isn't hom = not . getAny . getConst .  evalIxState (evalIxWriterT (hom (ireturn (Const (Any True)))))

-- TODO: Generlize this to s t a b 
matching :: IxMonadGet n => APrismF First n s t a a -> s -> Either t a
matching hom s = 
    case runIxState (evalIxWriterT (hom (igets pure))) s of
        (First (Just a), _) -> Right a
        (_, t)              -> Left t

-- Reviews

unto :: (b -> t) -> Prism' t b
unto f = prism' f (const Nothing)

un :: (IxMonadState n) => AGetter n s a -> Prism' a s
un getter = unto (^. getter)

re :: (IxMonadState n, IxMonadWriter n) => AReview n t b -> Getter b t
re rev = to (rev #)

(#) :: forall n s a. (IxMonadState n, IxMonadWriter n) => AReview n s a -> a -> s
(#) hom a = runIdentity (hom #! a)

(#!) :: forall m n s a. (IxMonadState n, IxMonadWriter n, Monad m) => AReviewM m n s a -> a -> m s
(#!) hom a
  | Just ms <- execIxWriterT (hom (imap pure (itell (return a))))
  = ms
  | otherwise = error "Bad review!"

infixr 8 #, #!