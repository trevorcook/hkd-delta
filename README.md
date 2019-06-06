# hkd-delta

A library for finding differences in higher kinded data (HKD).


```haskell
{-# LANGUAGE OverloadedStrings #-}
module Test where

import HKD.Delta
import GHC.Generics
import Generics.OneLiner
import Data.Text (Text)
import qualified Data.Text as T
```
The HasDelta class is central to this library, with it we declare how
differences in a type are measured, whether or not the differences
can always be measured, and functions for measuring and applying differences.
The below, for example, declares that 'Text' has a difference, 'Change Text',
(Where the 'Change' type is equivalent to 'Maybe'--but treated specially in
some cases by this library). The instance states that the difference will
allways be measurable, and the calc and apply methods just look for non-equal
values.

```haskell
instance HasDelta Text where
  type DeltaOf Text = Change Text
  type DeltaAlways Text = True
  calcDelta = calcDeltaNEQ
  applyDelta = applyDeltaNEQ

neqText = calcDelta @Text "a" "ab"
--neqTex = Changed "ab"
eqText = calcDelta @Text "a" "a"
-- eqText = Unchanged

```
Having defined a basic type, we next look at automatically generating
delta functionality for more interesting types.
First, we define a data type in Higher Kinded Data style
```haskell
type Citizen = Citizen' Z
data Citizen' f = Citizen { name        :: HK f Text
                          , occupation  :: HK f Text }
                    deriving Generic
deriving instance (Constraints (Citizen' f) Show)  --provided by one-liner
  => Show (Citizen' f)

```
Each field in our data is parameterized by a type constructor,
`f`, and a type function, `HK` which together control the expression of the
data at that field. A custom defined `Z` "escapes" from higher kinding,
allowing the data to just be itself. Another custom designed data,
`Delta` makes the data express the `DeltaReturn` of the data, which--
generally--is either a change in the data or a new copy of the data.
```haskell
data Z a
data Delta a
type family HK (f :: * -> *) (a :: *) :: * where
  HK Z a = a
  HK Delta a = DeltaReturn a

```
Next the `Citizen` is declared to have a delta, defined as
simply the `Citizen'` in the `Delta state`. This library is designed
to work with data such as this, and so no further definitions are needed.
DeltaAlways, calcDelta, and applyDelta are derived via Generic mechanisms.
instance HasDelta Citizen where
type DeltaOf Citizen = Citizen' Delta

Here we demonstrate a calculated difference between two
citizens, Mary and Mark.
```haskell
mary :: Citizen
mary = Citizen "Mary" "Police"
mark :: Citizen
mark = Citizen "Mark" "Police"
compMaryMark = calcDelta mary mark
-- compMaryMark = Citizen {name = Changed "Mark"
--                        , occupation = Unchanged}

```
Here we demonstrate the patching of a Citizen with a delta
```haskell
mayorMike :: Citizen
mayorMike = Citizen  "Mike" "Mayor"
mayorMark = applyDelta mayorMike compMaryMark
-- mayorMark = Citizen {name = "Mark", occupation = "Mayor"}

```
As noted, the 'Changed' constructor belongs to the `Change` type. And
this library provides special handling for Change deltas.
Speciffically, it allows `Unchanged` values to be propagated down a delta,
such that all unchanged fields result in an `Unchanged` delta.

For instance first observe the following delta is the same as Unchanged
```haskell
dMaryMary = calcDelta mary mary
-- dMaryMary = Citizen {name = Unchanged, occupation = Unchanged}
```
That is, if we apply it to any value, x, we must get, x.
applyDelta x dMaryMary == x

We can capture this equality by specifying the DeltaOf as a Change Type

```haskell
instance HasDelta Citizen where
  type DeltaOf Citizen = Change (Citizen' Delta)
```
the calculation dMaryMary now results in.
```haskell
-- dMaryMary = Unchanged

```
There is another special type, `Revise`, this libraries version of Either.
It is used when a data type has more than one construction.
```haskell
type Vehicle = Vehicle' Z
data Vehicle' f = Car { carType :: HK f Text }
               | CrashedCar { howBad :: HK f Text } deriving (Generic)
deriving instance (Constraints (Vehicle' f) Show)
  => Show (Vehicle' f)

instance HasDelta Vehicle where
  type DeltaOf Vehicle = Change (Vehicle' Delta)
  --type DeltaAlways = False (derived by a type family)

```
Now, two different Cars will result in an 'Update (DeltaOf)'

```haskell
colorDiff = calcDelta (Car "red" :: Vehicle) (Car "blue")
--colorDiff = Update (Changed (Car {carType = Changed "blue"}))

```
A difference in different constructors just returns the second value, since
the two different constructions cannot be generically compared.

```haskell
carDiff = calcDelta (Car "red"::Vehicle) (CrashedCar "very bad")
-- carDiff = Replace (CrashedCar {howBad = "very bad"})

```
Additionally, because `Revise` is traversable, we can quickly find that
whether or not a 'Revise a (Change b)' is a change.
```haskell
colorDiff' = sequenceA colorDiff
-- colorDiff' = Changed (Update (Car {carType = Changed "blue"}))
colorDiff'' = sequenceA $ calcDelta (Car "red" :: Vehicle)(Car "red" :: Vehicle)
-- colorDiff'' = Unchanged

```
