
module Test where

import HKD.Delta
import GHC.Generics
import Generics.OneLiner

-- Define a data type in Higher Kinded Data style
type Citizen = Citizen' Z
data Citizen' f = Citizen { name        :: HK f String
                          , occupation  :: HK f String }
                    deriving Generic
deriving instance (Constraints (Citizen' f) Show)  --provided by one-liner
  => Show (Citizen' f)

-- As usual. Each field in our data is parameterized by a type constructor,
-- `f`, and a type function, `HK` which together control the expression of the
-- data at that field. A custom defined `Z` "escapes" from higher kinding,
-- allowing the data to just be itself. Another custom designed data,
-- `Delta` makes the data expres the `DeltaReturn` of the data, which--
--generally--is either a change in the data or a new copy of the data. This
-- will be expanded upon.
data Z a
data Delta a
type family HK (f :: * -> *) (a :: *) :: * where
  HK Z a = a
  HK Delta a = DeltaReturn a

-- Next the `Citizen` is declared to have a "Delta", defined as
-- simply the `Citizen'` in the `Delta state`
-- instance HasDelta Citizen where
--   type DeltaOf Citizen = Citizen' Delta

-- The `HasDelta` class has two methods with generic defaults, which we
-- utilize here.
mary :: Citizen
mary = Citizen "Mary" "Garbage"
mark :: Citizen
mark = Citizen "Mark" "Garbage"
-- calcDelta :: a -> a -> DeltaReturn a
compMaryMark = calcDelta mary mark

-- The result: compMaryMark = Citizen {name = Changed "Mark"
--                                     , occupation = Unchanged}
-- shows the difference in the two is the name.
--
--The other method of `HasDelta` applies changes to values.
mayorMike :: Citizen
mayorMike = Citizen  "Mike" "Mayor"
-- applyDelta :: a -> DeltaReturn a -> a
mayorMark = applyDelta mayorMike compMaryMark
-- The result: mayorMark = Citizen {name = "Mark", occupation = "Mayor"}

-- Notice the 'Changed' constructor? It belons to the `Change` type provide by
-- this library. It the same as `Maybe`, but with special handling for deltas.
-- It allows `Unchanged` (Change's Nothing), to be propagated down a delta,
-- such that all unchanged fields result in an `Unchanged` delta.
--
-- For instance first observe
dMaryMary = calcDelta mary mary
-- dMaryMary = Citizen {name = Unchanged, occupation = Unchanged}
--The data is the same as itself, and if we were to redefine
--'DeltaOf' to detect the change with ...
instance HasDelta Citizen where
  type DeltaOf Citizen = Change (Citizen' Delta)
-- and try again
-- dMaryMary = Unchanged

--There is another special type, `Revise`, this librarys version of Either.
--It is used when a data type has more than one construction.
type Vehicle = Vehicle' Z
data Vehicle' f = Car { carType :: HK f String }
               | CrashedCar { howBad :: HK f String } deriving (Generic)
deriving instance (Constraints (Vehicle' f) Show)  --provided by one-liner
  => Show (Vehicle' f)
instance HasDelta Vehicle where
  type DeltaOf Vehicle = Change (Vehicle' Delta)

colorDiff = calcDelta (Car "red" :: Vehicle) (Car "blue")
--colorDiff = Update (Changed (Car {carType = Changed "blue"}))

--Because `Revise` is traversable, we can quickly find that
--the update is a change.
colorDiff' = sequenceA colorDiff
-- colorDiff' = Changed (Update (Car {carType = Changed "blue"}))
-- or not a change
colorDiff'' = sequenceA $ calcDelta (Car "red" :: Vehicle)(Car "red" :: Vehicle)
-- colorDiff'' = unchanged

-- A difference in different constructors returns the second value, since
-- the two different construcitons cannot be generically compared.
carDiff = calcDelta (Car "red"::Vehicle) (CrashedCar "very bad")
-- carDiff = Replace (CrashedCar {howBad = "very bad"})


--
--
--
-- data Protagonist = Hero | Sidekick deriving Show
-- data Antagonist = Villian | Henchman deriving Show
--
--
--
--
-- type family Point (k :: DeltaPointKind) (f :: * -> *) (a :: *) :: * where
--   Point f Z a = a
--   Point f Delta a = PointInDelta f a
--
-- type family PointInDelta (k :: DeltaPointKind) (a :: * ):: * where
--   PointInDelta StaticPointType a = Static a
--   PointInDelta DeltaPointType  a = DeltaReturn a
--
-- type DeltaPoint f a = Point DeltaPointType f a
-- type StaticPoint f a = Point StaticPointType f a
-- data DeltaPointKind = StaticPointType
--                     | DeltaPointType
--
--
--
--
--
--
--
--
--
--
--
--
--
-- type A = A' Z
-- data A' f = A (DeltaPoint f Int) (DeltaPoint f A)
--           | Ay (StaticPoint f Int)
--           | Ax
--           deriving Generic
-- instance HasDelta A where
--   type DeltaOf A = Change (A' Delta)
--
--
--
--
--
-- deriving instance (Constraints (A' f) Show) => Show (A' f)
-- a1,a2
--  ,ay1,ay2
--  , ax
--  :: A
-- a1 = A 1 ay1
-- a2 = A 2 ay1
-- ay1 = Ay 1
-- ay2 = Ay 2
-- ax = Ax
