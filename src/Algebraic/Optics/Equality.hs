-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Equality
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Equality
  ( Equality(..)
  , HasEquality(..) )
where

data Equality s t a b where
    Equality :: Equality s s a a

deriving instance Show (Equality s t a b)

class HasEquality s t a b where
  hasEquality :: Maybe (Equality s t a b)

instance {-# OVERLAPPING #-} (s ~ t) => HasEquality s t a a where
  hasEquality = Just Equality

instance {-# INCOHERENT #-} HasEquality s t a b where
  hasEquality = Nothing