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
import Algebraic.Optics.Type
import Control.Applicative

class Cons s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _Cons :: Prism s t (a, s) (b, t)

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
uncons _s = error "uncons" --s ^? _Cons

_head :: Cons s s a a => Traversal' s a
_head sm = 
    istateM $ \s ->
        case uncons s of
            Just (a, s) -> do
                (gx, b) <- runIxStateT sm a
                return (gx, cons b s)
            Nothing -> return (mempty1, s)

_tail :: Cons s s a a => Traversal' s s
_tail sm = 
    istateM $ \s -> 
        case uncons s of
            Just (a, s) -> do
                (gx, t) <- runIxStateT sm s
                return (gx, cons a t)
            Nothing -> return (mempty1, s)

class Snoc s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _Snoc :: Prism s t (s, a) (t, b)

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

_init :: Snoc s s a a => Traversal' s s
_init sm = 
    istateM $ \s ->
        case unsnoc s of
            Just (s, a) -> do
                (gx, t) <- runIxStateT sm s
                return (gx, snoc t a)
            Nothing -> return (mempty1, s)

_last :: Snoc s s a a => Traversal' s a
_last sm = 
    istateM $ \s ->
        case unsnoc s of
            Just (s, a) -> do
                (gx, b) <- runIxStateT sm a
                return (gx, snoc s b)
            Nothing -> return (mempty1, s)