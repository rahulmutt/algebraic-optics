-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Review
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Review where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Data.Monoid

infixr 8 #, #!

(#) :: forall n s a. (IxMonadState n, IxMonadWriter n) => AReview n s a -> a -> s
(#) hom a
  | Just s <- getIxReturn homResult
  = s
  | otherwise = error "Bad review"
  where homResult :: IxWriterT IxState s s s (First ())
        homResult = hom (imap pure (itell a))

(#!) :: forall m n s a. (IxMonadState n, IxMonadWriter n, Monad m) => AReviewM m n s a -> a -> m s
(#!) hom a
  | Just ms <- getIxReturn homResult
  = ms
  | otherwise = error "Bad review"
  where homResult :: IxWriterT (IxStateT m) (m s) s s (First ())
        homResult = hom (imap pure (itell (return a)))