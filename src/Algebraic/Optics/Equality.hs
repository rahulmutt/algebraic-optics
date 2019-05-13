-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Equality
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
{-# LANGUAGE PolyKinds #-}

module Algebraic.Optics.Equality
  ( Equality(..)
  , HasEquality(..) )
where

data Equality (s :: k1) (t :: k1) (a :: k2) (b :: k2) where
    Equality :: Equality s s a a
    NoEquality :: Equality s t a b

deriving instance Show (Equality s t a b)

class HasEquality (s :: k1) (t :: k1) (a :: k2) (b :: k2) where
  hasEquality :: Equality s t a b

instance {-# OVERLAPPING #-} (s ~ t) => HasEquality s t a a where
  hasEquality = Equality

instance {-# INCOHERENT #-} HasEquality s t a b where
  hasEquality = NoEquality