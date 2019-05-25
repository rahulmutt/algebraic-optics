-----------------------------------------------------------------------------
-- |
-- Module      :  Algebraic.Optics.Fold
-- Copyright   :  (C) 2019 Rahul Muttineni
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Rahul Muttineni <rahulmutt@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------

module Algebraic.Optics.Fold where

import Algebraic.Optics.Type
import Algebraic.Optics.Internal.Indexed

import Control.Applicative

import Data.Int
import Data.Monoid
import Data.Foldable
import Data.Functor.Identity

infixl 8 ^.., ^..!, ^?, ^?!, ^@.., ^@..!

(^..) :: IxMonadGet n => s -> AFold Endo n s a -> [a]
(^..) s hom = runIdentity (s ^..! hom)

(^..!) :: (IxMonadGet n, Monad m) => s -> AFoldM m Endo n s a -> m [a]
(^..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom (igets (Endo . (:)))) s)

(^?) :: IxMonadGet n => s -> AFold First n s a -> Maybe a
(^?) s hom = runIdentity (s ^?! hom)

(^?!) :: (IxMonadGet n, Monad m) => s -> AFoldM m First n s a -> m (Maybe a)
(^?!) s hom = fmap getFirst $ evalIxStateT (hom (igets pure)) s

has :: IxMonadGet n => AFold (Const Any) n s a -> s -> Bool
has hom = getAny . getConst . evalIxState (hom (igets (const (Const (Any True)))))

hasn't :: IxMonadGet n => AFold (Const All) n s a -> s -> Bool
hasn't hom = getAll . getConst . evalIxState (hom (igets (const (Const (All False)))))

folding :: Foldable f => (s -> f a) -> Fold s a
folding f sm = 
   igetsM $ foldlM (\b a -> fmap (b `mappend1`) (evalIxStateT sm a)) mempty1 . f

ifolding :: Foldable f => (s -> f (i, a)) -> IndexedFold i s a
ifolding f sm = 
   igetsM $ foldlM (\b (i, a) -> fmap (b `mappend1`) (evalIxReaderStateT sm i a)) mempty1 . f
   
folded :: Foldable f => IndexedFold Int (f a) a
folded = folded'

folded64 :: Foldable f => IndexedFold Int64 (f a) a
folded64 = folded'

folded' :: (Foldable f, Integral i) => IndexedFold i (f a) a
folded' sm = 
   igetsM $ fmap fst 
          . foldlM (\(b, !n) a -> do
                    b' <- evalIxReaderStateT sm n a
                    return (b `mappend1` b', n + 1))
                  (mempty1, 0)

unfolded :: (b -> Maybe (a, b)) -> Fold b a
unfolded f sm = igetsM go
   where go b 
           | Just (a, b') <- f b 
           = liftA2 mappend1 (evalIxStateT sm a) (go b')
           | otherwise 
           = return mempty1

iterated :: (a -> a) -> Fold1 a a
iterated f sm = igetsM go
   where go a = liftA2 mappend1 (evalIxStateT sm a) (go (f a))
   
filtered :: (a -> Bool) -> Fold a a
filtered f sm = 
   igetsM $ \a ->
      if f a
      then evalIxStateT sm a
      else return mempty1

reversed :: (Monoid1 f, IxFunctor m, IxFunctor n) => Optic m (ReverseMonoid f) n s t a b -> Optic m f n s t a b
reversed revHom sm = imap getReverseMonoid (revHom (imap ReverseMonoid sm))

repeated :: Fold1 a a
repeated sm = igetsM go
   where go a = liftA2 mappend1 (evalIxStateT sm a) (go a)

replicated :: Int -> Fold a a
replicated n sm = igetsM (go n)
   where go  0 _ = return mempty1
         go !n a = liftA2 mappend1 (evalIxStateT sm a) (go (n - 1) a)

cycled :: (Semigroup1 f, IxMonadState m) => Optic m f n s t a b -> Optic m f n s t a b
cycled hom sm = iget >>>= go
  where go s = hom sm >>>= (\gx -> 
               iput s >>>= (\_ ->
               go s >>>= (\hx ->
               ireturn (gx `mappend1` hx))))
   
takingWhile :: (Monoid1 f, IxFunctor m, IxMonadGet n) 
            => (a -> Bool) -> Optic m (TakingWhile f) n s t a a -> Optic m f n s t a a
takingWhile f hom sm = imap getTakingWhile (hom (iget >>>= decideTake))
   where decideTake a
           | f a       = imap TakingWhile sm
           | otherwise = ireturn (TakingWhileTerminated mempty1)

droppingWhile :: (Monoid1 f, IxFunctor m, IxMonadGet n) 
              => (a -> Bool) -> Optic m (DroppingWhile f) n s t a a -> Optic m f n s t a a
droppingWhile f hom sm = imap computeDroppingWhile (hom (iget >>>= decideDrop))
   where decideDrop a
           | f a       = imap DroppingWhileDropping sm
           | otherwise = imap DroppingWhile sm


foldMapOf :: (IxMonadGet n, Monoid r) => AFold (Const r) n s a -> (a -> r) -> s -> r
foldMapOf hom f = getConst . evalIxState (hom (igets (Const . f))) 

foldOf :: (IxMonadGet n, Monoid a) => AFold (Const a) n s a -> s -> a
foldOf hom = foldMapOf hom id

foldrOf :: IxMonadGet n => AFold Endo n s a -> (a -> r -> r) -> r -> s -> r
foldrOf hom f r = ($ r) . appEndo . evalIxState (hom (igets (Endo . f))) 

foldlOf :: IxMonadGet n => AFold (ReverseMonoid Endo) n s a -> (r -> a -> r) -> r -> s -> r
foldlOf hom f r = ($ r) . appEndo . getReverseMonoid . evalIxState (hom (igets (ReverseMonoid . Endo . flip f))) 

toListOf :: IxMonadGet n => AFold Endo n s a -> s -> [a]
toListOf hom s = s ^.. hom

anyOf :: IxMonadGet n => AFold (Const Any) n s a -> (a -> Bool) -> s -> Bool
anyOf hom f = getAny . getConst . evalIxState (hom (igets (Const . Any . f))) 

allOf :: IxMonadGet n => AFold (Const All) n s a -> (a -> Bool) -> s -> Bool
allOf hom f = getAll . getConst . evalIxState (hom (igets (Const . All . f))) 

noneOf :: IxMonadGet n => AFold (Const All) n s a -> (a -> Bool) -> s -> Bool
noneOf hom f = getAll . getConst . evalIxState (hom (igets (Const . All . not . f))) 

andOf :: IxMonadGet n => AFold (Const All) n s Bool -> s -> Bool
andOf sm = allOf sm id

orOf :: IxMonadGet n => AFold (Const Any) n s Bool -> s -> Bool
orOf sm = anyOf sm id

traverseOf_ :: (IxMonadGet n, Applicative f) => AFold (Traversed f) n s a  -> (a -> f r) -> s -> f ()
traverseOf_ hom f = getTraversed . evalIxState (hom (igets (\a -> Traversed (f a *> pure ())))) 

forOf_ :: (IxMonadGet n, Applicative f) => AFold (Traversed f) n s a -> s -> (a -> f r) -> f ()
forOf_ hom s f = traverseOf_ hom f s

sequenceAOf_ :: (IxMonadGet n, Applicative f) => AFold (Traversed f) n s (f r) -> s -> f ()
sequenceAOf_ hom = getTraversed . evalIxState (hom (igets (\a -> Traversed (a *> pure ())))) 

-- Indexed folds

(^@..) :: (IxMonadGet n, IxMonadReader i n) => s -> AFold Endo n s a -> [(i, a)]
(^@..) s hom = appEndo (evalIxState (hom (iwith (\i a -> Endo ((i, a) :)))) s) []

(^@..!) :: (IxMonadGet n, IxMonadReader i n, Monad m) => s -> AFoldM m Endo n s a -> m [(i, a)]
(^@..!) s hom = fmap (flip appEndo []) (evalIxStateT (hom (iwith (\i a -> Endo ((i, a) :)))) s)

(^@?) :: (IxMonadGet n, IxMonadReader i n) => s -> AFold First n s a -> Maybe (i, a)
(^@?) s hom = getFirst $ evalIxState (hom (iwith (\i a -> pure (i, a)))) s

(^@?!) :: (IxMonadGet n, IxMonadReader i n, Monad m) => s -> AFoldM m First n s a -> m (Maybe (i, a))
(^@?!) s hom = fmap getFirst $ evalIxStateT (hom (iwith (\i a -> pure (i, a)))) s

ifoldMapOf :: (IxMonadGet n, IxMonadReader i n, Monoid r) => AFold (Const r) n s a -> (i -> a -> r) -> s -> r
ifoldMapOf hom f = getConst . evalIxState (hom (iwith (\i a -> pure (f i a))))

ifoldrOf :: (IxMonadGet n, IxMonadReader i n) => AFold Endo n s a -> (i -> a -> r -> r) -> r -> s -> r
ifoldrOf hom f r = ($ r) . appEndo . evalIxState (hom (iwith (\i a -> Endo (f i a))))

ifoldlOf :: (IxMonadGet n, IxMonadReader i n) => AFold (ReverseMonoid Endo) n s a -> (i -> r -> a -> r) -> r -> s -> r
ifoldlOf hom f r = ($ r) . appEndo . getReverseMonoid . evalIxState (hom n) 
  where n = iwith (\i a -> ReverseMonoid (Endo (\r -> f i r a)))

itoListOf :: (IxMonadGet n, IxMonadReader i n) => AFold Endo n s a -> s -> [(i, a)]
itoListOf hom s = s ^@.. hom

ianyOf :: (IxMonadGet n, IxMonadReader i n) => AFold (Const Any) n s a -> (i -> a -> Bool) -> s -> Bool
ianyOf hom f = getAny . getConst . evalIxState (hom (iwith (\i a -> pure (Any (f i a)))))

iallOf :: (IxMonadGet n, IxMonadReader i n) => AFold (Const All) n s a -> (i -> a -> Bool) -> s -> Bool
iallOf hom f = getAll . getConst . evalIxState (hom (iwith (\i a -> pure (All (f i a))))) 

inoneOf :: (IxMonadGet n, IxMonadReader i n) => AFold (Const All) n s a -> (i -> a -> Bool) -> s -> Bool
inoneOf hom f = getAll . getConst . evalIxState (hom (iwith (\i a -> pure (All (not (f i a)))))) 

ifiltered :: (i -> a -> Bool) -> IndexPreservingFold i a a
ifiltered f sm = 
   iwithM (\i a -> 
      if f i a
      then evalIxReaderStateT sm i a
      else return mempty1)

itakingWhile :: (Monoid1 f, IxFunctor m, IxMonadGet n, IxMonadReader i n) 
            => (i -> a -> Bool) -> Optic m (TakingWhile f) n s t a a -> Optic m f n s t a a
itakingWhile f hom sm = imap getTakingWhile (hom (iask >>>= (\i -> iget >>>= (\a -> decideTake i a))))
   where decideTake i a
           | f i a     = imap TakingWhile sm
           | otherwise = ireturn (TakingWhileTerminated mempty1)

idroppingWhile :: (Monoid1 f, IxFunctor m, IxMonadGet n, IxMonadReader i n) 
               => (i -> a -> Bool) -> Optic m (DroppingWhile f) n s t a a -> Optic m f n s t a a
idroppingWhile f hom sm = imap computeDroppingWhile (hom (iask >>>= (\i -> iget >>>= (\a -> decideDrop i a))))
   where decideDrop i a
           | f i a     = imap DroppingWhileDropping sm
           | otherwise = imap DroppingWhile sm
           
-- Helper Monoids

data TakingWhile f a =
    TakingWhile { getTakingWhile :: f a }
  | TakingWhileTerminated { getTakingWhile :: f a }

instance (Semigroup1 f) => Semigroup1 (TakingWhile f) where
    mappend1 (TakingWhile m1) (TakingWhile m2) = TakingWhile (m1 `mappend1` m2)
    mappend1 (TakingWhile m1) (TakingWhileTerminated m2) = TakingWhileTerminated (m1 `mappend1` m2)
    mappend1 m@(TakingWhileTerminated _) _ = m

instance (Monoid1 f) => Monoid1 (TakingWhile f) where
    mempty1 = TakingWhile mempty1

data DroppingWhile f a =
    DroppingWhileDropping { getDroppingWhile :: f a }
  | DroppingWhile { getDroppingWhile :: f a }
  | DroppingWhileTaking { getDropped :: f a, getDroppingWhile :: f a }

instance (Monoid1 f) => Semigroup1 (DroppingWhile f) where
    mappend1 (DroppingWhileTaking d1 m1) m2 = DroppingWhileTaking d1 (m1 `mappend1` getDroppingWhile m2)
    mappend1 (DroppingWhileDropping d1) (DroppingWhile m2) = DroppingWhileTaking d1 m2
    mappend1 (DroppingWhileDropping d1) (DroppingWhileTaking d2 m2) = DroppingWhileTaking (d1 `mappend1` d2) m2
    mappend1 (DroppingWhileDropping d1) (DroppingWhileDropping d2) = DroppingWhileDropping (d1 `mappend1` d2)
    mappend1 (DroppingWhile m1) (DroppingWhileTaking d2 m2) = DroppingWhileTaking mempty1 (m1 `mappend1` (d2 `mappend1` m2))
    mappend1 (DroppingWhile m1) m2 = DroppingWhile (m1 `mappend1` getDroppingWhile m2)

instance (Monoid1 f) => Monoid1 (DroppingWhile f) where
    mempty1 = DroppingWhileDropping mempty1

computeDroppingWhile :: (Monoid1 f) => DroppingWhile f a -> f a
computeDroppingWhile (DroppingWhileDropping _) = mempty1
computeDroppingWhile (DroppingWhileTaking _ fa) = fa
computeDroppingWhile (DroppingWhile fa) = fa

newtype Traversed f a = Traversed { getTraversed :: f () }

instance (Applicative f) => Semigroup1 (Traversed f) where
    mappend1 (Traversed m1) (Traversed m2) = Traversed (m1 *> m2)

instance (Applicative f) => Monoid1 (Traversed f) where
    mempty1 = Traversed (pure ())