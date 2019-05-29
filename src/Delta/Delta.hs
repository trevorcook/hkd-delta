{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Delta.Delta where

-- import Data.Either
import Data.Semigroup
import Data.Bifunctor
import GHC.Generics
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Void
import Control.Applicative

--- DEV Imports
---
import Generics.OneLiner



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
isChanged :: Change a -> Bool
isChanged Unchanged = False
isChanged _ = True
changedToMaybe :: Change a-> Maybe a
changedToMaybe (Changed a) = Just a
changedToMaybe _ = Nothing
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

data SigChange a = SigUnchanged a | SigChanged a
 deriving Functor
instance Applicative SigChange where
  pure = SigUnchanged
  (SigUnchanged f) <*> (SigUnchanged a) = SigUnchanged (f a)
  (SigUnchanged f) <*> (SigChanged a) = SigChanged (f a)
  (SigChanged f) <*> (SigUnchanged a) = SigChanged (f a)
  (SigChanged f) <*> (SigChanged a) = SigChanged (f a)
sigChange :: (a -> b) -> (a -> b) -> SigChange a -> b
sigChange u _ (SigUnchanged a) = u a
sigChange _ c (SigChanged a)   = c a




-- NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
-- NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
type DeltaCtx a = DeltaCtx_ (DeltaOf a)
type family DeltaCtx_ (dlt :: * ) :: * -> * where
  DeltaCtx_ (Revise a b) = Revise a
  DeltaCtx_ (Change (Revise a b)) =  Compose Change (Revise a)
  DeltaCtx_ (Change c) =  Change
  DeltaCtx_ x          = Identity

class HasDelta a where
  type DeltaOf a
  calcDeltaOf    :: a -> a -> DeltaOf a
  default calcDeltaOf :: ( HasDeltaVia (DeltaCtx a) a (DeltaOf a) ) =>
     a -> a -> DeltaOf a
  calcDeltaOf = calcDeltaVia @(DeltaCtx a)

class HasDeltaVia (ctx :: * -> *) a d where
  calcDeltaVia :: a -> a -> d

instance  ( Generic a, Generic d
          , HasDeltaGen SigChange (Rep a) (Rep d)) =>
  HasDeltaVia Identity a d where
  calcDeltaVia a a' = sigChange to to
                    $ calcDeltaGen @SigChange (from a) (from a')

instance  ( Generic a, Generic d
          , HasDeltaGen (Compose Maybe SigChange) (Rep a) (Rep d)) =>
  HasDeltaVia  (Compose Change (Revise a)) a (Change (Revise a d)) where
  calcDeltaVia a a' = maybe (Changed $ Replace a')
                            (sigChange (const Unchanged)
                                       (Changed . Update . to))
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe SigChange) (from a) (from a')
instance  ( Generic a, Generic d
          , HasDeltaGen (Compose Maybe SigChange) (Rep a) (Rep d)) =>
  HasDeltaVia  (Revise a) a (Revise a d) where
  calcDeltaVia a a' = maybe (Replace a')
                            (sigChange (Update . to)
                                       (Update . to))
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe SigChange) (from a) (from a')


class HasDeltaGen ctx a d where
  calcDeltaGen :: a p -> a p -> ctx (d p)
  -- applyDeltaGen :: c p -> d p -> Maybe (c p)

instance               (Functor f, HasDeltaGen f a d) =>
  HasDeltaGen f (M1 t x a) (M1 t x d) where
  calcDeltaGen a a' = M1 <$> calcDeltaGen @f (unM1 a) (unM1 a')
instance               (HasDelta a, DeltaOf a ~ Change d) =>
  HasDeltaGen SigChange (K1 x a) (K1 x (Change d)) where
  calcDeltaGen a a' = change (SigUnchanged $ K1 Unchanged)
                             (SigChanged . K1. Changed)
                    $ calcDeltaOf (unK1 a) (unK1 a')
instance
  HasDeltaGen SigChange (K1 x a) (K1 x (Static a)) where
  calcDeltaGen a a' = SigUnchanged $ K1 Static
instance  {-#Overlappable#-}        (HasDelta a, DeltaOf a ~ d) =>
  HasDeltaGen SigChange (K1 x a) (K1 x d) where
  calcDeltaGen a a' = SigChanged . K1
                    $ calcDeltaOf (unK1 a) (unK1 a')
instance                ( HasDeltaGen ctx al dl
                        , HasDeltaGen ctx ar dr
                        , Applicative ctx) =>
  HasDeltaGen ctx (al :*: ar) (dl :*: dr) where
  calcDeltaGen (al :*: ar) (al' :*: ar')
    = (:*:)
      <$> calcDeltaGen @ctx al al'
      <*> calcDeltaGen @ctx ar ar'
instance                ( HasDeltaGen SigChange al dl
                        , HasDeltaGen SigChange ar dr
                        ) =>
  HasDeltaGen (Compose Maybe SigChange) (al :+: ar) (dl :+: dr) where
  calcDeltaGen (L1 a) (L1 a') = Compose . Just
                              $ L1 <$> calcDeltaGen @SigChange a a'
  calcDeltaGen (R1 a) (R1 a') = Compose . Just
                              $ R1 <$> calcDeltaGen @SigChange a a'
  calcDeltaGen _       _      = Compose Nothing



-- | Only never Change
instance HasDelta () where
  type DeltaOf () = Static ()
  calcDeltaOf _ _ = Static

-- | Effectually enum types, detects different "constructor"
calcDeltaOfNEQ :: Eq a => a -> a -> Change a
calcDeltaOfNEQ a b | a == b = Unchanged
                   | otherwise = Changed b
instance HasDelta Bool where
  type DeltaOf Bool = Change Bool
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta Int where
  type DeltaOf Int = Change Int
  calcDeltaOf = calcDeltaOfNEQ
-- instance HasDelta Double where
--   type DeltaOf Double = ()
  -- type DeltaCtx
--   calcDeltaOf = calcDeltaOfNEQ
-- instance HasDelta Char where
--   type DeltaOf Char = ()
--   calcDeltaOf = calcDeltaOfNEQ
instance HasDelta String where
  type DeltaOf String = Change String
  calcDeltaOf = calcDeltaOfNEQ





-- class HasDelta0 a where
--   nullify :: a -> Change a
--   default nullify :: (Generic a, HasDelta0Gen (Rep a)) =>
--     a -> Change a
--   nullify = fmap to . nullifyGen . from
-- instance HasDelta0 () where
--   nullify _ = Unchanged
-- instance HasDelta0 (Static a) where
--   nullify _ = Unchanged
-- instance HasDelta0 a => HasDelta0 (Identity a) where
--   nullify = traverse nullify
-- instance HasDelta0 (Change a) where
--   nullify = fmap Changed
-- instance HasDelta0 a => HasDelta0 (Maybe a) where
--   nullify = traverse nullify
-- instance HasDelta0 a => HasDelta0 [a] where
--   nullify = nullifyAny
-- instance HasDelta0 u => HasDelta0 (Revise r u) where
--   nullify = traverse nullify
--
-- nullifyAny :: (Foldable f, HasDelta0 a) => f a -> Change (f a)
-- nullifyAny as | any (isChanged . nullify) as = Changed as
--               | otherwise                    = Unchanged
--
--
--
data Z a
data Static a = Static deriving (Generic,Show,Functor)
data Delta a

data DeltaPointKind = StaticPointType
                    | DeltaPointType

type family Point (k :: DeltaPointKind) (f :: * -> *) (a :: *) :: * where
  Point f Z a = a
  Point f Delta a = PointInDelta f a

type family PointInDelta (k :: DeltaPointKind) (a :: * ):: * where
  PointInDelta StaticPointType a = Static a
  PointInDelta DeltaPointType  a = DeltaOf a

type DeltaPoint f a = Point DeltaPointType f a
type StaticPoint f a = Point StaticPointType f a

type A = A' Z
data A' f = A (DeltaPoint f Int) (DeltaPoint f Int)
          | Ay (StaticPoint f Int)
          deriving Generic
instance HasDelta A where
  type DeltaOf A = Change (Revise A (A' Delta))

deriving instance (Constraints (A' f) Show) => Show (A' f)
a1,a2
 ,ay1,ay2
 :: A
a1 = A 1 2
a2 = A 2 2
ay1 = Ay 1
ay2 = Ay 2
