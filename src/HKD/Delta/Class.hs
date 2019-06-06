module HKD.Delta.Class
  ( HasDelta(..)
  , DeltaReturn
  , calcDeltaNEQ
  , applyDeltaNEQ
  )where

import HKD.Delta.Type

import GHC.Generics
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Type.Bool
import Data.Type.Equality

-- | Types which can be \"diffed\" and \"patched\".
class HasDelta a where
  -- | Specifies how differences in data are measured. This type must
  --   be defined.
  type DeltaOf a

  -- | Used to signal whether or not @calcDelta a1 a2@ always results in
  --   @d :: DeltaOf a@.
  --
  -- This does not need to be defined for @Generic@ data. If the data
  -- is a single constructor, the delta should always be calculatable,
  -- and the return type is 'True'.
  type DeltaAlways a :: Bool
  type DeltaAlways a = NotSumRep (Rep a)
  -- | Find the difference between two instances of a data.
  calcDelta    :: a -> a -> DeltaReturn a
  default calcDelta ::
    HasDeltaVia (DeltaAlways a) a (DeltaReturn a) =>
     a -> a -> DeltaReturn a
  calcDelta = calcDeltaVia @(DeltaAlways a) @a @(DeltaReturn a)

  -- | Patch a data with difference.
  applyDelta    :: a -> DeltaReturn a -> a
  default applyDelta ::
    HasDeltaVia (DeltaAlways a) a (DeltaReturn a) =>
     a -> DeltaReturn a -> a
  applyDelta = applyDeltaVia @(DeltaAlways a) @a @(DeltaReturn a)

-- |The result of a delta calculation. For @DeltaAlways a = True@,
-- this is just @DeltaOf@. For @DeltaAlways a = False@ this
-- resolves to @Revise a (DeltaOf a)@
type DeltaReturn a = If (DeltaAlways a) (DeltaOf a) (Revise a (DeltaOf a))

type family NotSumRep a :: Bool where
  NotSumRep (M1 t x (a :+: b)) = False
  NotSumRep x                  = True


-- A Helper Class to handle the various delta return types: those with
-- single constructors (DeltaAlways = True), and those with multiple
-- For both those categories, one instance detects "Older" data, returning
-- "Unchanged" if the DeltaOf type is also "Unchanged"
class HasDeltaVia (ctx :: Bool) a d where
  calcDeltaVia :: a -> a -> d
  applyDeltaVia :: a -> d -> a
instance                            ( Generic a, Generic d
                                    , HasDeltaGen Freshest (Rep a) (Rep d)) =>
  HasDeltaVia  True a (Change d) where
  calcDeltaVia a a' = freshest (const Unchanged) (Changed . to)
                    $ calcDeltaGen @Freshest (from a) (from a')
  applyDeltaVia a = change a (to . applyDeltaGen (from a) . Newer . from)
instance {-#Overlappable#-}         ( Generic a, Generic d
                                    , HasDeltaGen Freshest (Rep a) (Rep d)) =>
  HasDeltaVia True a d where
  calcDeltaVia a a' = freshest to to
                    $ calcDeltaGen @Freshest (from a) (from a')
  applyDeltaVia a = to . applyDeltaGen (from a) . Newer . from
instance  ( Generic a, Generic d
          , HasDeltaGen (Compose Maybe Freshest) (Rep a) (Rep d)) =>
  HasDeltaVia False a (Revise a (Change d)) where
  calcDeltaVia a a' = maybe (Replace a')
                            (freshest (const $ Update Unchanged)
                                      (Update . Changed . to))
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe Freshest) (from a) (from a')
  applyDeltaVia a = revise id (change a (to . applyDeltaGen (from a)
                                            . Compose . Just . Newer . from))
instance {-#Overlappable#-}         ( Generic a, Generic d
                  , HasDeltaGen (Compose Maybe Freshest) (Rep a) (Rep d)) =>
  HasDeltaVia False a (Revise a d) where
  calcDeltaVia a a' = maybe (Replace a') (Update . freshest to to)
                    . getCompose
                    $ calcDeltaGen @(Compose Maybe Freshest) (from a) (from a')
  applyDeltaVia a = revise id (to . applyDeltaGen (from a)
                                  . Compose . Just . Newer . from)



-- Freshest is used in the generic implementations to signal wheter or not
-- data in the fields are Changed or Unchanged. It allows an Unchaged at the
-- top level if all fields are unchanged, otherwise doing nothing.
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
  applyDeltaGen :: a p -> ctx (d p) -> a p
instance               (Functor f, HasDeltaGen f a d) =>
  HasDeltaGen f (M1 t x a) (M1 t x d) where
  calcDeltaGen a a' = M1 <$> calcDeltaGen @f (unM1 a) (unM1 a')
  applyDeltaGen a d = M1 $ applyDeltaGen (unM1 a) (unM1 <$> d)
instance               (HasDelta a, DeltaReturn a ~ Change d) =>
  HasDeltaGen Freshest (K1 x a) (K1 x (Change d)) where
  calcDeltaGen a a' = change (Older $ K1 Unchanged)
                             (Newer . K1. Changed)
                    $ calcDelta (unK1 a) (unK1 a')
  applyDeltaGen = applyAnyFreshnessK1
instance               ( HasDelta a, DeltaReturn a ~ f (Change d)
                       , Traversable f) =>
  HasDeltaGen Freshest (K1 x a) (K1 x (f (Change d))) where
  calcDeltaGen a a' = (\r -> change (Older (K1 r))
                                    (const $ Newer (K1 r))
                             $ sequenceA r)
                    $ calcDelta (unK1 a) (unK1 a')
  applyDeltaGen = applyAnyFreshnessK1
instance
  HasDeltaGen Freshest (K1 x a) (K1 x (Static b)) where
  calcDeltaGen a a' = Older $ K1 Static
  applyDeltaGen a _ = a
instance  {-#Overlappable#-}        (HasDelta a, DeltaReturn a ~ d) =>
  HasDeltaGen Freshest (K1 x a) (K1 x d) where
  calcDeltaGen a a' = Newer . K1
                    $ calcDelta (unK1 a) (unK1 a')
  applyDeltaGen = applyAnyFreshnessK1
instance                ( HasDeltaGen ctx al dl
                        , HasDeltaGen ctx ar dr
                        , Applicative ctx) =>
  HasDeltaGen ctx (al :*: ar) (dl :*: dr) where
  calcDeltaGen (al :*: ar) (al' :*: ar')
    = (:*:)
      <$> calcDeltaGen @ctx al al'
      <*> calcDeltaGen @ctx ar ar'
  applyDeltaGen (al :*: ar) d =  (applyDeltaGen al $ lProd <$> d)
                             :*: (applyDeltaGen ar $ rProd <$> d)
    where
      lProd (a :*: _) = a
      rProd (_ :*: b) = b
instance    ( HasDeltaGen (Compose Maybe Freshest) (all :+: alr) (dll :+: dlr)
            , HasDeltaGen (Compose Maybe Freshest) (arl :+: arr) (drl :+: drr)
            ) =>
  HasDeltaGen (Compose Maybe Freshest) ((all :+: alr) :+: (arl :+: arr))
                                       ((dll :+: dlr) :+: (drl :+: drr)) where
  calcDeltaGen (L1 a) (L1 a')
    = L1 <$> calcDeltaGen @(Compose Maybe Freshest) a a'
  calcDeltaGen (R1 a) (R1 a')
    = R1 <$> calcDeltaGen @(Compose Maybe Freshest) a a'
  calcDeltaGen _       _      = Compose Nothing
  applyDeltaGen s = maybe s (freshest (goSum (Compose . Just . Older)
                                             (Compose . Just . Older) s)
                                      (goSum (Compose . Just . Newer)
                                             (Compose . Just . Newer) s))
                  . getCompose

instance {-#Overlappable#-}
            ( HasDeltaGen Freshest al dl
            , HasDeltaGen (Compose Maybe Freshest) (arl :+: arr) (drl :+: drr)
            ) =>
  HasDeltaGen (Compose Maybe Freshest) (al :+: (arl :+: arr))
                                       (dl :+: (drl :+: drr)) where
  calcDeltaGen (L1 a) (L1 a')
    = Compose . Just $ L1 <$> calcDeltaGen @Freshest a a'
  calcDeltaGen (R1 a) (R1 a')
    = R1 <$> calcDeltaGen @(Compose Maybe Freshest) a a'
  calcDeltaGen _       _      = Compose Nothing
  applyDeltaGen s = maybe s (freshest (goSum Older (Compose . Just . Older) s)
                                      (goSum Newer (Compose . Just . Newer) s))
                  . getCompose
instance {-#Overlappable#-}
            ( HasDeltaGen (Compose Maybe Freshest) (all :+: alr) (dll :+: dlr)
            , HasDeltaGen Freshest ar dr
            ) =>
  HasDeltaGen (Compose Maybe Freshest) ((all :+: alr) :+: ar)
                                       ((dll :+: dlr) :+: dr) where
  calcDeltaGen (L1 a) (L1 a')
    = L1 <$> calcDeltaGen @(Compose Maybe Freshest) a a'
  calcDeltaGen (R1 a) (R1 a')
    = Compose . Just $ R1 <$> calcDeltaGen @Freshest a a'
  calcDeltaGen _       _      = Compose Nothing
  applyDeltaGen s = maybe s (freshest (goSum (Compose . Just . Older) Older s)
                                      (goSum (Compose . Just . Newer) Newer s))
                  . getCompose
instance {-#Overlappable#-}   ( HasDeltaGen Freshest al dl
                              , HasDeltaGen Freshest ar dr
                              ) =>
  HasDeltaGen (Compose Maybe Freshest) (al :+: ar) (dl :+: dr) where
  calcDeltaGen (L1 a) (L1 a') = Compose . Just
                              $ L1 <$> calcDeltaGen @Freshest a a'
  calcDeltaGen (R1 a) (R1 a') = Compose . Just
                              $ R1 <$> calcDeltaGen @Freshest a a'
  calcDeltaGen _       _      = Compose Nothing
  applyDeltaGen s = maybe s (freshest (goSum Older Older s)
                                      (goSum Newer Newer s))
                  . getCompose


instance HasDeltaGen Freshest U1 U1 where
  calcDeltaGen _ _ = Older U1
  applyDeltaGen _ _ = U1
instance HasDeltaGen Freshest V1 V1 where
  calcDeltaGen _ _ = undefined
  applyDeltaGen _ _ = undefined


applyAnyFreshnessK1 :: HasDelta a =>
  K1 x a p -> Freshest (K1 x (DeltaReturn a) p) -> K1 x a p
applyAnyFreshnessK1 a = K1 . freshest go go
    where go d = applyDelta (unK1 a) (unK1 d)

goSum ::                    ( HasDeltaGen f al dl
                            , HasDeltaGen g ar dr ) =>
  (forall x . x -> f x) -> (forall x . x -> g x) ->
  (al :+: ar) p -> ((dl :+: dr) p) -> (al :+: ar) p
goSum f _ (L1 a) (L1 d) = L1 $ applyDeltaGen a (f d)
goSum _ g (R1 a) (R1 d) = R1 $ applyDeltaGen a (g d)
goSum _ _  s      _     = s



-- | Only never Change
instance HasDelta () where
  type DeltaOf () = Static ()
  calcDelta _ _ = Static
  applyDelta _ _ = ()

-- | Method to calculate delta for simple types.
calcDeltaNEQ :: Eq a => a -> a -> Change a
calcDeltaNEQ a b | a == b = Unchanged
                 | otherwise = Changed b
-- | Method to apply simple changes. Either replaces with the change or
--   returns the original.
applyDeltaNEQ :: a -> Change a -> a
applyDeltaNEQ a = change a id

instance HasDelta Bool where
  type DeltaOf Bool = Change Bool
  type DeltaAlways Bool = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
instance HasDelta Char where
  type DeltaOf Char = Change Char
  type DeltaAlways Char = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
instance HasDelta Double where
  type DeltaOf Double = Change Double
  type DeltaAlways Double = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
instance HasDelta Float where
  type DeltaOf Float = Change Float
  type DeltaAlways Float = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
instance HasDelta Int where
  type DeltaOf Int = Change Int
  type DeltaAlways Int = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
instance HasDelta Integer where
  type DeltaOf Integer = Change Integer
  type DeltaAlways Integer = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ
-- instance HasDelta String where
--   type DeltaOf String = Change String
--   type DeltaAlways String = True
--   calcDelta = calcDeltaNEQ
--   applyDelta = applyDeltaNEQ
