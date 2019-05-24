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

module Delta.Delta where

-- import Data.Either
import Data.Semigroup
import Data.Bifunctor
import GHC.Generics
import Data.Functor.Identity

--- DEV Imports
---
import Generics.OneLiner
-- data NoChange
  -- type MustChange a :: Bool
  -- type MustChange a = True
  -- type MustCalc a :: Bool
  -- type MustCalc a = False
-- type DeltaReturn a = DeltaReturn_ a (MustCalc a) (MustChange a)
-- type family DeltaReturn a (x::Bool) (y::Bool) where
--   DeltaReturn a True True = DeltaOf a
--   DeltaReturn a True False = Either () (DeltaOf a)
--   DeltaReturn a False True = Maybe (DeltaOf a)
--   DeltaReturn a False False = Maybe (Either () (DeltaOf a))


data  Changed a = Unchanged | Changed a deriving (Show,Functor)
instance Applicative Changed where
  pure = Changed
  Changed f <*> Changed a = Changed $ f a
  _ <*> _ = Unchanged
instance Semigroup a => Semigroup (Changed a) where
  Changed a <> Changed b = Changed (a <> b)
  Unchanged <> b = b
  a <> Unchanged = a
instance Semigroup a => Monoid (Changed a) where
  mempty = Unchanged
instance Foldable Changed where
  foldr f b (Changed a) = f a b
  foldr _ b _ = b
  foldMap em (Changed a) = em a
  foldMap _  (Unchanged) = mempty

instance Traversable Changed where
  traverse f (Changed a) = Changed <$> f a
  traverse _ _   = pure Unchanged
isChanged :: Changed a -> Bool
isChanged Unchanged = False
isChanged _ = True
-- changedToMaybe :: Changed a-> Maybe a
-- changedToMaybe (Changed a) = Just a
-- changedToMaybe _ = Nothing
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


newtype CtxDeltaOnly a = CtxDeltaOnly (DeltaOf a)
newtype CtxDeltaChanged a = CtxDeltaChanged (Changed (DeltaOf a))
newtype CtxPatchPoint a = CtxPatchChanged (Changed (PatchOf a))

class (CanPatch (DeltaCtx a)) => HasDelta a where
  type DeltaOf a
  type DeltaCtx a :: * -> *
  type DeltaCtx a = Maybe
  calcDeltaOf    :: a -> a -> DeltaCtx a (DeltaOf a)
  default calcDeltaOf :: ( Generic a, Generic (DeltaOf a)
                         , HasDeltaGen (DeltaCtx a) (Rep a) (Rep (DeltaOf a))
                         ) =>
     a -> a -> DeltaCtx a (DeltaOf a)
  calcDeltaOf a = fmap to . calcDeltaGen @(DeltaCtx a) (from a) . from

  -- calcDeltaPoint    :: a -> a -> Maybe (Changed (DeltaOf a))
  -- applyDeltaOf :: a -> DeltaOf a -> Maybe a

type PatchOf a = Revise a (DeltaOf a)

calcPatchOf :: HasDelta a => a -> a -> PatchOf a
calcPatchOf a a' = maybe (Replace a') Update . toMaybeCtx $ calcDeltaOf a a'

class (Functor f) => CanPatch f where
  toMaybeCtx :: f a -> Maybe a
instance CanPatch Maybe where
  toMaybeCtx = id
instance CanPatch Identity where
  toMaybeCtx = Just . runIdentity

class HasDelta0 a where
  nullify :: a -> Changed a
  default nullify :: (Generic a, HasDelta0Gen (Rep a)) =>
    a -> Changed a
  nullify = fmap to . nullifyGen . from
instance HasDelta0 () where
  nullify _ = Unchanged
instance HasDelta0 (Static a) where
  nullify _ = Unchanged
instance HasDelta0 a => HasDelta0 (Identity a) where
  nullify = traverse nullify
instance HasDelta0 (Changed a) where
  nullify = fmap Changed
instance HasDelta0 a => HasDelta0 (Maybe a) where
  nullify = traverse nullify
instance HasDelta0 a => HasDelta0 [a] where
  nullify = nullifyAny
instance HasDelta0 u => HasDelta0 (Revise r u) where
  nullify = traverse nullify

nullifyAny :: (Foldable f, HasDelta0 a) => f a -> Changed (f a)
nullifyAny as | any (isChanged . nullify) as = Changed as
              | otherwise                    = Unchanged


-- calcPatchPoint ::                     (HasDelta a) =>
--   a -> a -> PatchPoint a
-- calcPatchPoint a a' = sequenceA . maybe (Left a') Right $ calcPatch a a'

-- calcPatchPoint ::                     (HasDelta a) =>
--   a -> a -> PatchPoint a
-- calcPatchPoint a a' = maybe (Left a') Right $ calcDeltaOf a a'
data Z a
data Static a = Static deriving (Generic,Show,Functor)
data Delta a
data DeltaPointKind = StaticPointType
                    -- | DeltaPointType
                    | PatchPointType
type family Point (k :: DeltaPointKind) (f :: * -> *) (a :: *) :: * where
  Point f Z a = a
  Point f Delta a = PointInDelta f a
type family PointInDelta (k :: DeltaPointKind) (a :: * ):: * where
  PointInDelta StaticPointType a = Static a
  -- PointInDelta DeltaPointType  a = Changed (DeltaOf a)
  PointInDelta PatchPointType  a = Changed (PatchOf a)

-- type DeltaPoint f a = Point DeltaPointType f a
type PatchPoint f a = Point PatchPointType f a
type StaticPoint f a = Point StaticPointType f a

type A = A' Z
data A' f = A (PatchPoint f Int) (PatchPoint f Int)
          | Ay (StaticPoint f Int) deriving Generic
instance HasDelta0 (A' Delta)
instance HasDelta A where
  type DeltaOf A = A' Delta
  type DeltaCtx A = Maybe
deriving instance (Constraints (A' f) Show) => Show (A' f)
a1,a2,ay1,ay2 :: A
a1 = A 1 1
a2 = A 2 1
ay1 = Ay 1
ay2 = Ay 1

class Functor ctx => HasDeltaGen ctx a d where
  calcDeltaGen :: a p -> a p -> ctx (d p)
  -- applyDeltaGen :: c p -> d p -> Maybe (c p)

instance        (Applicative ctx , HasDelta a, PatchOf a ~ Revise a d ) =>
  HasDeltaGen ctx (K1 x a) (K1 x (Revise a d)) where
  calcDeltaGen a a' =  pure . K1 $ calcPatchOf (unK1 a) (unK1 a')
instance        (Applicative ctx, HasDelta a, PatchOf a ~ Revise a d, HasDelta0 d ) =>
  HasDeltaGen ctx (K1 x a) (K1 x (Changed (Revise a d))) where
  calcDeltaGen a a' =  pure . K1 . nullify $ calcPatchOf (unK1 a) (unK1 a')
instance        (Applicative ctx) =>
  HasDeltaGen ctx (K1 x a) (K1 x (Static b)) where
  calcDeltaGen a a' =  pure $ K1 Static
instance                ( HasDeltaGen ctx al dl
                        , HasDeltaGen ctx ar dr
                        , Applicative ctx) =>
  HasDeltaGen ctx (al :*: ar) (dl :*: dr) where
  calcDeltaGen (al :*: ar) (al' :*: ar') = (:*:)
                                      <$> calcDeltaGen @ctx al al'
                                      <*> calcDeltaGen @ctx ar ar'
instance                ( HasDeltaGen Maybe al dl
                        , HasDeltaGen Maybe ar dr ) =>
  HasDeltaGen Maybe (al :+: ar) (dl :+: dr) where
  calcDeltaGen (L1 a) (L1 a') = L1 <$> calcDeltaGen a a'
  calcDeltaGen (R1 a) (R1 a') = R1 <$> calcDeltaGen a a'
  calcDeltaGen _       _      = Nothing
instance               (HasDeltaGen ctx a d) =>
  HasDeltaGen ctx (M1 t x a) (M1 t x d) where
  calcDeltaGen c d = M1 <$> calcDeltaGen @ctx (unM1 c) (unM1 d)


class HasDelta0Gen a where
  nullifyGen :: a p -> Changed (a p)
instance        (HasDelta0 a) =>
  HasDelta0Gen (K1 x a) where
  nullifyGen = fmap K1 . nullify . unK1
instance        ( HasDelta0Gen a ) =>
  HasDelta0Gen  (M1 t x a) where
  nullifyGen =  fmap M1 . nullifyGen . unM1
instance        ( HasDelta0Gen a, HasDelta0Gen b ) =>
  HasDelta0Gen (a :*: b) where
  nullifyGen (a :*: b) = (a :*: b)
                       <$  (( () <$ nullifyGen a) <> (() <$ nullifyGen b))
instance        ( HasDelta0Gen a, HasDelta0Gen b ) =>
  HasDelta0Gen (a :+: b) where
  nullifyGen l@(L1 a) = l <$ nullifyGen a
  nullifyGen r@(R1 a) = r <$ nullifyGen a
-- instance        ( HasDelta0Gen a, HasDelta0Gen b ) =>
--   HasDelta0Gen (U1 x) where
--   nullifyGen l@(L1 a) = l <$ nullifyGen a
--   nullifyGen r@(R1 a) = r <$ nullifyGen a


-- | Only never Change
instance HasDelta () where
  type DeltaOf () = ()
  calcDeltaOf _ _ = Just ()

-- | Effectually enum types, detects different "constructor"
calcDeltaOfNEQ :: Eq a => a -> a -> Maybe ()
calcDeltaOfNEQ a b | a == b = Just ()
                   | otherwise = Nothing
instance HasDelta Bool where
  type DeltaOf Bool = ()
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta Int where
  type DeltaOf Int = ()
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta Double where
  type DeltaOf Double = ()
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta Char where
  type DeltaOf Char = ()
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta String where
  type DeltaOf String = ()
  calcDeltaOf = calcDeltaOfNEQ
