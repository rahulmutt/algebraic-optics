-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Lens
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Lens where

import Algebraic.Optics.Type
import Algebraic.Optics.Equality
import Algebraic.Optics.Internal.Indexed

import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import Control.Arrow

lens :: (s -> a) -> (s -> b -> t) -> ALens s t a b
lens getter setter sm = istateM (\s -> fmap (second (setter s)) (runIxStateT sm (getter s)))

mlens :: forall m s t a b. HasEquality s t a b => (s -> m a) -> (s -> a -> Bool -> m s) -> (s -> b -> m t) -> ALensM m s t a b
mlens getter msetter psetter sm = 
    iget >>>= (\s -> 
    ilift (getter s) >>>= (\a ->
    ilift (runIxStateInstrumentT sm a) >>>= (\(r, b, c) ->
    case (hasEquality :: Equality s t a b) of
        Equality -> 
            ilift (msetter s b c) >>>= (\t ->
            iput t >>>= (\_ ->
            ireturn r))
        NoEquality -> 
            ilift (psetter s b) >>>= (\t ->
            iput t >>>= (\_ ->
            ireturn r)))))

mlens' :: (s -> m a) -> (s -> b -> Bool -> m t) -> ALensM m s t a b
mlens' getter setter sm = 
    iget >>>= (\s -> 
    ilift (getter s) >>>= (\a ->
    ilift (runIxStateInstrumentT sm a) >>>= (\(r, b, c) ->
    ilift (setter s b c) >>>= (\t ->
    iput t >>>= (\_ ->
    ireturn r)))))

mrefLens :: (s -> IORef a) -> ALensIO' s a
mrefLens f = mlens' getter setter
   where getter s = liftIO (readIORef (f s))
         setter s b modified = do
            when modified $
              liftIO (writeIORef (f s) b)
            return s

prefLens :: HasEquality s t a b => (s -> IORef a) -> (s -> IORef b -> t) -> ALensIO s t a b
prefLens f g = mlens getter msetter psetter
   where getter s = liftIO (readIORef (f s))
         msetter s b modified = do
            when modified $
              liftIO (writeIORef (f s) b)
            return s
         psetter s b = do
            ref <- liftIO (newIORef b)
            return (g s ref)