-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Cons
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Cons where

import Algebraic.Optics.Internal.Indexed
--import Algebraic.Optics.Fold
import Algebraic.Optics.Prism
import Algebraic.Optics.Review
import Algebraic.Optics.Type
import Control.Applicative

class Cons s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _Cons :: APrism s t (a, s) (b, t)

instance Cons [a] [b] a b where
    _Cons = prism (uncurry (:))
                  (\case (x:xs) -> Right (x, xs)
                         []     -> Left [])

instance Cons (ZipList a) (ZipList b) a b where
    _Cons = prism (\(b, ZipList t) -> ZipList (b:t))
                  (\zl -> case getZipList zl of
                            (x:xs) -> Right (x, ZipList xs)
                            []     -> Left  (ZipList []))
            
cons :: Cons s s a a => a -> s -> s
cons a s = _Cons # (a, s) 

uncons :: Cons s s a a => s -> Maybe (a, s)
uncons _s = undefined -- s ^? _Cons

_head :: Cons s s a a => ATraversal' s a
_head sm = iget >>>= (\s -> 
    case uncons s of
        Just (a, s) -> 
            let (gx, b) = runIxState sm a
            in iput (cons b s) >>>= const (ireturn gx)
        Nothing -> ireturn mempty1)

_tail :: Cons s s a a => ATraversal' s s
_tail sm = iget >>>= (\s -> 
    case uncons s of
        Just (a, s) -> 
            let (gx, t) = runIxState sm s
            in iput (cons a t) >>>= const (ireturn gx)
        Nothing -> ireturn mempty1)

class Snoc s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _Snoc :: APrism s t (s, a) (t, b)

instance Snoc [a] [b] a b where
    _Snoc = prism (\(t,b) -> t ++ [b])
                  (\s -> 
                   if null s
                   then Left []
                   else Right (init s, last s))
                   -- TODO: Inefficient. Use a fold.

instance Snoc (ZipList a) (ZipList b) a b where
    _Snoc = prism (\(ZipList t, b) -> ZipList (t ++ [b]))
                  (\zl -> 
                    let s = getZipList zl in 
                    if null s 
                    then Left (ZipList [])
                    else Right (ZipList (init s), last s))
                   -- TODO: Inefficient. Use a fold.

snoc :: Snoc s s a a => s -> a -> s
snoc s a = _Snoc # (s, a) 

unsnoc :: Snoc s s a a => s -> Maybe (s, a)
unsnoc _s = undefined -- s ^? _Snoc

_init :: Snoc s s a a => ATraversal' s s
_init sm = iget >>>= (\s -> 
    case unsnoc s of
        Just (s, a) -> 
            let (gx, t) = runIxState sm s
            in iput (snoc t a) >>>= const (ireturn gx)
        Nothing -> ireturn mempty1)

_last :: Snoc s s a a => ATraversal' s a
_last sm = iget >>>= (\s -> 
    case unsnoc s of
        Just (s, a) -> 
            let (gx, b) = runIxState sm a
            in iput (snoc s b) >>>= const (ireturn gx)
        Nothing -> ireturn mempty1)