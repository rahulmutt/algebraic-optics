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
import Algebraic.Optics.Internal.Indexed

import Unsafe.Coerce
import Data.Maybe

prism :: forall s t a b. (b -> t) -> (s -> Either t a) -> APrism s t a b 
prism f g sm' = 
    itell t >>>= (\_ ->
    istateM (\s -> 
        case g s of
            Left  t -> return (mempty1, t)
            Right a -> do
                (r, b) <- runIxStateT sm a 
                return (r, f b)))
    where (mret, sm) = runIxWriterT sm'
          t = f (unsafeCoerce (fromJust mret) :: b)

prismM :: forall m s t a b. (b -> m t) -> (s -> m (Either t a)) -> APrismM m s t a b 
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

prism' :: (b -> s) -> (s -> Maybe a) -> APrism s s a b 
prism' f g = prism f (\s -> maybe (Left s) Right $ g s)

_Just :: APrism (Maybe a) (Maybe b) a b
_Just = prism Just (maybe (Left Nothing) Right)

_Nothing :: APrism' (Maybe a) ()
_Nothing = prism' (const Nothing) (maybe (Just ()) (const Nothing))