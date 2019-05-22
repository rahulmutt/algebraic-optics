-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
module Algebraic.Optics 
  ( module X
  , (&)
  )
where

import Algebraic.Optics.Equality  as X
import Algebraic.Optics.Fold      as X
import Algebraic.Optics.Getter    as X
import Algebraic.Optics.Lens      as X
import Algebraic.Optics.Prism     as X
import Algebraic.Optics.Review    as X
import Algebraic.Optics.Setter    as X
import Algebraic.Optics.Traversal as X
import Algebraic.Optics.Type      as X

import Data.Function ((&))