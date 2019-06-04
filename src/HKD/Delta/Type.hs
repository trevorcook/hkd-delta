module HKD.Delta.Type
  ( Static(..)
  , Change(..), change
  , Revise(..), revise
  ) where

import Data.Bifunctor
import GHC.Generics

data Static a = Static deriving (Generic,Show,Functor)

data  Change a = Unchanged | Changed a deriving (Show,Functor)
instance Applicative Change where
  pure = Changed
  Changed f <*> Changed a = Changed $ f a
  _ <*> _ = Unchanged
instance Semigroup a => Semigroup (Change a) where
  Changed a <> Changed b = Changed (a <> b)
  Unchanged <> b = b
  a <> Unchanged = a
instance Semigroup a => Monoid (Change a) where
  mempty = Unchanged
instance Foldable Change where
  foldr f b (Changed a) = f a b
  foldr _ b _ = b
  foldMap em (Changed a) = em a
  foldMap _  (Unchanged) = mempty
instance Traversable Change where
  traverse f (Changed a) = Changed <$> f a
  traverse _ _   = pure Unchanged
change ::  b ->  (a -> b) -> Change a -> b
change _ f (Changed a) = f a
change b _ _           = b

data Revise r u = Replace r | Update u
  deriving (Generic,Show,Eq,Functor)
revise :: (r -> z) -> (u -> z) -> Revise r u -> z
revise f _ (Replace r) = f r
revise _ g (Update u)  = g u
instance Applicative (Revise r) where
  pure u = Update u
  Update f <*> Update u = Update (f u)
  Replace r <*> Update _ = Replace r
  _        <*> Replace r = Replace r
instance Foldable (Revise r) where
  foldr f b (Update a) = f a b
  foldr _ b _ = b
  foldMap em (Update a) = em a
  foldMap _  (Replace _) = mempty
instance Traversable (Revise r) where
  traverse f (Update a) = Update <$> f a
  traverse _ (Replace r)  = pure (Replace r)
instance Bifunctor Revise where
  bimap f g = revise (Replace . f) (Update . g)
instance Semigroup (Revise r (r -> r)) where
  _ <> Replace r = Replace r
  Replace r <> Update u = Replace (u r)
  Update u <> Update u' = Update (u' . u)
instance Monoid (Revise r (r -> r)) where
  mempty = Update id
