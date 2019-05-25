-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Iso
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Iso where

import Algebraic.Optics.Type
import Algebraic.Optics.Prism
import Algebraic.Optics.Internal.Indexed

import Data.Functor.Identity
import Data.Maybe
import Unsafe.Coerce
import Data.Coerce
import Data.Bifunctor

iso :: (s -> a) -> (b -> t) -> Iso s t a b 
iso f g = isoM (Identity . f) (Identity . g)

isoM :: forall m s t a b. (s -> m a) -> (b -> m t) -> IsoM m s t a b 
isoM f g sm' =
    itell t >>>= (\_ ->
    istateM (\s -> do
        a      <- f s
        (r, b) <- runIxStateT sm a 
        t      <- g b
        return (r, t)))
    where (mret, sm) = runIxWriterT sm'
          t = (unsafeCoerce (fromJust mret) :: m b) >>= g

from :: ARawIso s t a b -> Iso b a t s
from i = withIso i $ \sa bt -> iso bt sa

cloneIso :: ARawIso s t a b -> Iso s t a b
cloneIso i = withIso i iso

withIso :: (IxMonadState n, IxMonadWriter (Identity b) n) => AnIso n s t a b -> ((s -> a) -> (b -> t) -> r) -> r 
withIso iso f = f (unsafeTo iso) (unsafeFrom iso)

unsafeTo :: (IxMonadState n, IxMonadWriter (Identity b) n) => AnIso n s t a b -> s -> a
unsafeTo hom s = runIdentity $ fmap runIdentity $ evalIxStateT (evalIxWriterT (hom n)) s
  where n = istate (\a -> (Identity a, undefined))

unsafeFrom :: (IxMonadState n, IxMonadWriter (Identity b) n) => AnIso n s t a b -> b -> t
unsafeFrom iso b
  | Just s <- execIxWriterT (iso (imap (pure :: () -> Unit ()) 
                            (itell (Identity b) >>>= const (iput b))))
  = runIdentity s
  | otherwise = error "Bad unsafeReview"

au :: (IxMonadState n, IxMonadWriter (Identity b) n, Functor f) => AnIso n s t a b -> ((b -> t) -> f s) -> f a 
au iso btfs = withIso iso $ \sa bt -> fmap sa (btfs bt)

under :: (IxMonadState n, IxMonadWriter (Identity b) n) => AnIso n s t a b -> (t -> s) -> b -> a 
under iso f b = withIso iso $ \sa bt -> sa (f (bt b))

mapping :: (IxMonadState n, IxMonadWriter (Identity b) n, Functor f, Functor g) => AnIso n s t a b -> Iso (f s) (g t) (f a) (g b) 
mapping i = withIso i $ \sa bt -> iso (fmap sa) (fmap bt)

non :: Eq a => a -> Iso' (Maybe a) a 
non a = iso (fromMaybe a) (\a0 -> if a == a0 then Just a0 else Nothing)

non' :: ARawPrism' a () -> Iso' (Maybe a) a 
non' prism = 
    withPrism prism $ \bt sta -> 
        iso (fromMaybe (bt ())) 
            (\a -> either (const Nothing) (const (Just a)) (sta a))

anon :: a -> (a -> Bool) -> Iso' (Maybe a) a 
anon a f = iso (fromMaybe a) (\a0 -> if f a0 then Just a0 else Nothing)

enum :: Enum a => Iso' Int a 
enum = iso toEnum fromEnum

curried :: Iso ((a, b) -> c) ((d, e) -> f) (a -> b -> c) (d -> e -> f) 
curried = iso curry uncurry

uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a, b) -> c) ((d, e) -> f) 
uncurried = iso uncurry curry

flipped :: Iso (a -> b -> c) (a' -> b' -> c') (b -> a -> c) (b' -> a' -> c') 
flipped = iso flip flip

involuted :: (a -> a) -> Iso' a a 
involuted f = iso f f

bimapping :: (IxMonadState n, IxMonadWriter (Identity b) n,
              IxMonadState n', IxMonadWriter (Identity b') n',
              Bifunctor f, Bifunctor g) 
          => AnIso n s t a b 
          -> AnIso n' s' t' a' b' 
          -> Iso (f s s') (g t t') (f a a') (g b b') 
bimapping iso1 iso2 =
    withIso iso1 $ \sa1 bt1 ->
        withIso iso2 $ \sa2 bt2 ->
            iso (bimap sa1 sa2) (bimap bt1 bt2)

firsting :: (IxMonadState n, IxMonadWriter (Identity b) n, Bifunctor f, Bifunctor g) 
         => AnIso n s t a b 
         -> Iso (f s x) (g t y) (f a x) (g b y) 
firsting i = withIso i $ \sa bt -> iso (first sa) (first bt)

seconding :: (IxMonadState n, IxMonadWriter (Identity b) n, Bifunctor f, Bifunctor g) 
          => AnIso n s t a b 
          -> Iso (f x s) (g y t) (f x a) (g y b) 
seconding i = withIso i $ \sa bt -> iso (second sa) (second bt)

coerced :: (Coercible s a, Coercible t b) => Iso s t a b 
coerced = iso coerce coerce