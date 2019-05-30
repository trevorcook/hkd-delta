module Delta.Delta where

import Delta.Type

import GHC.Generics
import Data.Functor.Identity
import Data.Functor.Compose

data Z a
data Static a = Static deriving (Generic,Show,Functor)
data Delta a

class HasDelta a where
  type DeltaOf a
  type DeltaReturnType a :: DeltaReturnKind
  type DeltaReturnType a = CalcDeltaReturnType a
  calcDeltaOf    :: a -> a -> DeltaReturn a
  default calcDeltaOf ::
    HasDeltaVia (DeltaReturnType a) a (DeltaReturn a) =>
     a -> a -> DeltaReturn a
  calcDeltaOf = calcDeltaVia @(DeltaReturnType a) @a @(DeltaReturn a)

data DeltaReturnKind = DeltaAlways | DeltaMaybe
type DeltaReturn a = DeltaReturn_ a (DeltaReturnType a)
type family DeltaReturn_ a (t::DeltaReturnKind) where
  DeltaReturn_ a DeltaAlways = DeltaOf a
  DeltaReturn_ a DeltaMaybe = Maybe (DeltaOf a)
type CalcDeltaReturnType a = CalcDeltaReturnType_ a (IsSumRep (Rep a))
type family CalcDeltaReturnType_ a (b::Bool) :: DeltaReturnKind where
  CalcDeltaReturnType_ a True = DeltaMaybe
  CalcDeltaReturnType_ a False = DeltaAlways
type family IsSumRep a :: Bool where
  IsSumRep (M1 t x (a :+: b)) = True
  IsSumRep x                  = False

-- class HasPatch a where
--   calcPatchOf :: a -> a -> Revise a (DeltaOf a)
-- instance HasPatchVia (DeltaCtx a) a => HasPatch a where
--   calcPatchOf = calcPatchVia @(DeltaCtx a)
-- class HasDelta a => HasPatchVia ctx a where
--   calcPatchVia :: a -> a -> Revise a (DeltaOf a)
-- instance (HasDelta a, DeltaCtx a ~ Maybe) =>
--   HasPatchVia Maybe a where
--   calcPatchVia a a' = maybe (Replace a') Update
--                     $ calcDeltaOf a a'
-- instance (HasDelta a, DeltaCtx a ~ Identity) => HasPatchVia Identity a where
--   calcPatchVia a = Update . calcDeltaOf a
--
-- type DeltaCtx a = DeltaCtx_ (DeltaOf a)
-- type family DeltaCtx_ (dlt :: * ) :: * -> * where
--   DeltaCtx_ (Revise a b) = Revise a
--   DeltaCtx_ (Change (Revise a b)) =  Compose Change (Revise a)
--   DeltaCtx_ (Change c) =  Change
--   DeltaCtx_ x          = Identity

class HasDeltaVia (ctx :: DeltaReturnKind) a d where
  calcDeltaVia :: a -> a -> d

instance                            ( Generic a, Generic d
                                    , HasDeltaGen Freshest (Rep a) (Rep d)) =>
  HasDeltaVia  DeltaAlways a (Change d) where
  calcDeltaVia a a' = freshest (const Unchanged) (Changed . to)
                    $ calcDeltaGen @Freshest (from a) (from a')
instance {-#Overlappable#-}         ( Generic a, Generic d
                                    , HasDeltaGen Freshest (Rep a) (Rep d)) =>
  HasDeltaVia DeltaAlways a d where
  calcDeltaVia a a' = freshest to to
                    $ calcDeltaGen @Freshest (from a) (from a')

instance  ( Generic a, Generic d
          , HasDeltaGen (Compose Maybe Freshest) (Rep a) (Rep d)) =>
  HasDeltaVia DeltaMaybe a (Maybe (Change d)) where
  calcDeltaVia a a' = fmap (freshest (const Unchanged) (Changed . to))
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe Freshest) (from a) (from a')
instance {-#Overlappable#-}         ( Generic a, Generic d
                  , HasDeltaGen (Compose Maybe Freshest) (Rep a) (Rep d)) =>
  HasDeltaVia DeltaMaybe a (Maybe d) where
  calcDeltaVia a a' = fmap (freshest to to)
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe Freshest) (from a) (from a')




data Freshest a = Older a | Newer a
 deriving Functor
instance Applicative Freshest where
  pure = Older
  (Older f) <*> (Older a) = Older (f a)
  (Older f) <*> (Newer a) = Newer (f a)
  (Newer f) <*> (Older a) = Newer (f a)
  (Newer f) <*> (Newer a) = Newer (f a)
freshest :: (a -> b) -> (a -> b) -> Freshest a -> b
freshest u _ (Older a) = u a
freshest _ c (Newer a)   = c a



class HasDeltaGen ctx a d where
  calcDeltaGen :: a p -> a p -> ctx (d p)
  -- applyDeltaGen :: c p -> d p -> Maybe (c p)

instance               (Functor f, HasDeltaGen f a d) =>
  HasDeltaGen f (M1 t x a) (M1 t x d) where
  calcDeltaGen a a' = M1 <$> calcDeltaGen @f (unM1 a) (unM1 a')
instance               (HasDelta a, DeltaReturn a ~ Change d) =>
  HasDeltaGen Freshest (K1 x a) (K1 x (Change d)) where
  calcDeltaGen a a' = change (Older $ K1 Unchanged)
                             (Newer . K1. Changed)
                    $ calcDeltaOf (unK1 a) (unK1 a')
instance
  HasDeltaGen Freshest (K1 x a) (K1 x (Static a)) where
  calcDeltaGen a a' = Older $ K1 Static
instance  {-#Overlappable#-}        (HasDelta a, DeltaReturn a ~ d) =>
  HasDeltaGen Freshest (K1 x a) (K1 x d) where
  calcDeltaGen a a' = Newer . K1
                    $ calcDeltaOf (unK1 a) (unK1 a')
instance                ( HasDeltaGen ctx al dl
                        , HasDeltaGen ctx ar dr
                        , Applicative ctx) =>
  HasDeltaGen ctx (al :*: ar) (dl :*: dr) where
  calcDeltaGen (al :*: ar) (al' :*: ar')
    = (:*:)
      <$> calcDeltaGen @ctx al al'
      <*> calcDeltaGen @ctx ar ar'
instance                ( HasDeltaGen Freshest al dl
                        , HasDeltaGen Freshest ar dr
                        ) =>
  HasDeltaGen (Compose Maybe Freshest) (al :+: ar) (dl :+: dr) where
  calcDeltaGen (L1 a) (L1 a') = Compose . Just
                              $ L1 <$> calcDeltaGen @Freshest a a'
  calcDeltaGen (R1 a) (R1 a') = Compose . Just
                              $ R1 <$> calcDeltaGen @Freshest a a'
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
  type DeltaReturnType Bool = DeltaAlways
  calcDeltaOf = calcDeltaOfNEQ
instance HasDelta Int where
  type DeltaOf Int = Change Int
  type DeltaReturnType Int = DeltaAlways
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
  type DeltaReturnType String = DeltaAlways
  calcDeltaOf = calcDeltaOfNEQ
