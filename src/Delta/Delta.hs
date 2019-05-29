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
  calcDeltaOf    :: a -> a -> DeltaOf a
  default calcDeltaOf :: ( HasDeltaVia (DeltaCtx a) a (DeltaOf a) ) =>
     a -> a -> DeltaOf a
  calcDeltaOf = calcDeltaVia @(DeltaCtx a)

type DeltaCtx a = DeltaCtx_ (DeltaOf a)
type family DeltaCtx_ (dlt :: * ) :: * -> * where
  DeltaCtx_ (Revise a b) = Revise a
  DeltaCtx_ (Change (Revise a b)) =  Compose Change (Revise a)
  DeltaCtx_ (Change c) =  Change
  DeltaCtx_ x          = Identity

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
