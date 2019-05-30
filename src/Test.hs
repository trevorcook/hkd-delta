
module Test where

import Delta
import GHC.Generics
--- DEV Imports
---
import Generics.OneLiner


data DeltaPointKind = StaticPointType
                    | DeltaPointType

type family Point (k :: DeltaPointKind) (f :: * -> *) (a :: *) :: * where
  Point f Z a = a
  Point f Delta a = PointInDelta f a

type family PointInDelta (k :: DeltaPointKind) (a :: * ):: * where
  PointInDelta StaticPointType a = Static a
  PointInDelta DeltaPointType  a = DeltaReturn a

type DeltaPoint f a = Point DeltaPointType f a
type StaticPoint f a = Point StaticPointType f a

type A = A' Z
data A' f = A (DeltaPoint f Int) (DeltaPoint f A)
          | Ay (StaticPoint f Int)
          deriving Generic
instance HasDelta A where
  type DeltaOf A = Change (A' Delta)

deriving instance (Constraints (A' f) Show) => Show (A' f)
a1,a2
 ,ay1,ay2
 :: A
a1 = A 1 ay1
a2 = A 2 ay1
ay1 = Ay 1
ay2 = Ay 2
