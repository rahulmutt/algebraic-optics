-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.At
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.At where

import Algebraic.Optics.Internal.Indexed
import Algebraic.Optics.Setter
import Algebraic.Optics.Type
import Control.Monad.Reader

type family Key kv

type family Value kv

class Keyed kv => At kv where
    at :: Key kv -> ALens' kv (Maybe (Value kv))

delete :: At kv => Key kv -> kv -> kv
delete k = at k .~ Nothing

iat :: At kv => Key kv -> AIndexedLens' (Key kv) kv (Maybe (Value kv))
iat k sm = at k (iget >>>= f)
 where f a = iput b >>>= const (ireturn gx)
         where (gx, b) = runReader (runIxStateT sm a) k 

class Keyed kv where
    key :: Key kv -> ATraversal' kv (Value kv)
    
    default key :: At kv => Key kv -> ATraversal' kv (Value kv)
    key = keyAt

keyAt :: At kv => Key kv -> ATraversal' kv (Value kv)
keyAt k sm = at k (iget >>>= f)
 where f (Just a) = iput (Just b) >>>= const (ireturn gx)
         where (gx, b) = runIxState sm a
       f Nothing = ireturn mempty1

ikey :: Keyed kv => Key kv -> AIndexedTraversal' (Key kv) kv (Value kv)
ikey k sm = key k (iget >>>= f)
 where f a = iput b >>>= const (ireturn gx)
         where (gx, b) = runReader (runIxStateT sm a) k 

class Contains t where
    contains :: Key t -> ALens' t Bool

icontains :: Contains t => Key t -> AIndexedLens' (Key t) t Bool
icontains k sm = contains k (iget >>>= f)
 where f a = iput b >>>= const (ireturn gx)
         where (gx, b) = runReader (runIxStateT sm a) k 