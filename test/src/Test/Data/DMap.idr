module Test.Data.DMap

import Data.List
import Data.Singleton
import Data.Vect
import Derive.Prelude

import Tester
import Tester.Runner

import Data.DMap
import Data.DSum
import Data.GEq
import Data.GCompare

%language ElabReflection

data K : Nat -> Type where
  MkK : Char -> (n : Nat) -> K n

%runElab derive "K" [Show]

V : Nat -> Type
V n = Vect n Char

unsafeGEQ : GOrdering a b
unsafeGEQ = believe_me $ the (GOrdering 0 0) GEQ

unsafeBoolToMEq : Bool -> Maybe (a = b)
unsafeBoolToMEq True = Just (believe_me $ the (0 = 0) Refl)
unsafeBoolToMEq False = Nothing

unsafeOrderingToGOrdering : Ordering -> GOrdering a b
unsafeOrderingToGOrdering LT = GLT
unsafeOrderingToGOrdering EQ = unsafeGEQ
unsafeOrderingToGOrdering GT = GGT

implementation GEq K where
  geq (MkK i1 a) (MkK i2 b) = unsafeBoolToMEq ((i1, a) == (i2, b))

implementation GEq V where
  geq xs ys = unsafeBoolToMEq (toList xs == toList ys)

implementation GCompare K where
  gcompare (MkK i1 a) (MkK i2 b) = unsafeOrderingToGOrdering (compare (i1, a) (i2, b))

implementation GCompare V where
  gcompare xs ys = unsafeOrderingToGOrdering (compare (toList xs) (toList ys))

-- TODO get rid of this, define `GShow` etc.
implementation Show (DSum K V) where
  show (k :=> v) = show k ++ " :=> " ++ show v

-- TODO get rid of this, define `Show` for `DMap`
implementation Show (DMap K V) where
  show dmap = "fromList " ++ show (toList dmap)

-- Test Data
k00, k10, k20 : K 0
ka0 = MkK 'a' 0
kb0 = MkK 'b' 0
kc0 = MkK 'c' 0

ka1, kb1, kc1 : K 1
ka1 = MkK 'a' 1
kb1 = MkK 'b' 1
kc1 = MkK 'c' 1

ka2, kb2, kc2 : K 2
ka2 = MkK 'a' 2
kb2 = MkK 'b' 2
kc2 = MkK 'c' 2

va0, vb0, vc0 : V 0
va0 = []
vb0 = []
vc0 = []

va1, vb1, vc1 : V 1
va1 = ['a']
vb1 = ['b']
vc1 = ['c']

va2, vb2, vc2 : V 2
va2 = ['a', 'a']
vb2 = ['b', 'b']
vc2 = ['c', 'c']

kva0, kvb0, kvc0, kva1, kvb1, kvc1, kva2, kvb2, kvc2 : DSum K V

kva0 = ka0 :=> va0
kvb0 = kb0 :=> vb0
kvc0 = kc0 :=> vc0

kva1 = ka1 :=> va1
kvb1 = kb1 :=> vb1
kvc1 = kc1 :=> vc1

kva2 = ka2 :=> va2
kvb2 = kb2 :=> vb2
kvc2 = kc2 :=> vc2

allPairs : List (DSum K V)
allPairs = [kva0, kvb0, kvc0, kva1, kvb1, kvc1, kva2, kvb2, kvc2]

||| Assert that the elements of the list are exactly the elements of the map
||| @ elems the list
||| @ dmap  the map
assertElems : (elems : List (DSum K V)) -> (dmap : DMap K V) -> TestFunc ()
assertElems elems dmap = assertEq (sort elems) (sort $ toList dmap)

namespace FromList

  fromEmpty : Test
  fromEmpty
    = test "make a map from an empty list"
    $ assertEq empty (the (DMap K V) (fromList []))

  fromSingleton : Test
  fromSingleton
    = test "make a map from singleton list"
    $ assertEq (singleton ka0 va0) (fromList [kva0])

  fromAllPairs : Test
  fromAllPairs
    = test "make a map from a multi-element list"
    $ assertElems allPairs (fromList allPairs)

  export
  tests : List Test
  tests = [fromEmpty, fromSingleton, fromAllPairs]

namespace Eq
  reflexiveEmpty : Test
  reflexiveEmpty
    = test "`empty == empty`"
    $ let
      dmap : DMap K V
      dmap = empty
      in assertEq dmap dmap

  reflexiveNonEmpty : Test
  reflexiveNonEmpty
    = test "`dmap == dmap`"
    $ let
      dmap = DMap.fromList allPairs
      in assertEq dmap dmap

  reversedEqualsItself : Test
  reversedEqualsItself
    = test "`fromList l == fromList (reverse l)`"
    $ assertEq (DMap.fromList allPairs) (fromList $ reverse allPairs)

  emptyNonEmpty : Test
  emptyNonEmpty
    = test "`empty /= dmap` where `dmap` is non-empty"
    $ let dmap = fromList allPairs
      in assertNotEq DMap.empty dmap

  differentElems : Test
  differentElems
    = test "maps constructed from different elements are not equal"
    $ let
      lhs = DMap.fromList (take 3 allPairs)
      rhs = DMap.fromList (drop 6 allPairs)
      in assertNotEq lhs rhs

  export
  tests : List Test
  tests
    = [ reflexiveEmpty
      , reflexiveNonEmpty
      , reversedEqualsItself
      , emptyNonEmpty
      , differentElems
      ]

namespace Insert
  insert1 : Test
  insert1
    = test "insert 1 element"
    $ assertElems [kva0] (insert ka0 va0 empty)

  insert2Different : Test
  insert2Different
    = test "insert 2 pairs with different parameter"
    $ let
      dmap = insert ka0 va0
           . insert ka1 va1
           $ empty
    in assertElems [kva0, kva1] dmap

  insert2Same : Test
  insert2Same
    = test "insert 2 pairs with the same parameter"
    $ let
      dmap = insert ka0 va0
           . insert kb0 vb0
           $ empty
    in assertElems [kva0, kvb0] dmap

  insertTheSamPairTwice : Test
  insertTheSamPairTwice
    = test "insert the same pair twice"
    $ let
      dmap = insert ka0 va0
           . insert ka0 va0
           $ empty
    in assertElems [kva0] dmap

  insertTheSameKeyTwice : Test
  insertTheSameKeyTwice
    = test "insert 2 pairs with the same key"
    $ let
      dmap = insert kb0 va0
           . insert kb0 vb0
           $ empty
    in assertElems [kvb0] dmap

  insertAllPairs : Test
  insertAllPairs
    = test "insert multiple pairs"
    $ let
      dmap : DMap K V
      dmap = foldr (\(k :=> v) => insert k v) empty allPairs
    in assertElems allPairs dmap

  export
  tests : List Test
  tests
    = [ insert1
      , insert2Different
      , insert2Same
      , insertTheSamPairTwice
      , insertTheSameKeyTwice
      , insertAllPairs
      ]

namespace Lookup
  lookupSingle : Test
  lookupSingle
    = test "`lookup` in sinlgetom"
    $ let
      dmap : DMap K V
      dmap = singleton ka1 va1
    in assertEq (lookup ka1 dmap) (Just va1)

  lookupIn9Elems : Test
  lookupIn9Elems
    = test "lookup in a 9-element map"
    $ let
      dmap : DMap K V
      dmap = fromList allPairs
      in assertEq (lookup kb1 dmap) (Just vb1)


  lookupEmpty : Test
  lookupEmpty
    = test "lookup in empty map"
    $ let
      dmap : DMap K V
      dmap = empty
      in assertEq (lookup ka0 dmap) Nothing

  lookupNonExistent : Test
  lookupNonExistent
    = test "lookup a non-existent key"
    $ let
      dmap : DMap K V
      dmap = fromList [kvb0, kvb1, kvb2]
      in assertEq (lookup ka0 dmap) Nothing

  export
  tests : List Test
  tests
    = [ lookupSingle
      , lookupIn9Elems
      , lookupEmpty
      , lookupNonExistent
      ]

namespace Delete
  delete1 : Test
  delete1
    = test "delete 1 element"
    $ let
      dmap : DMap K V
      dmap = fromList [kva0, kvb1, kvc2]
      in assertElems [kva0, kvb1] (delete kc2 dmap)

  deleteFromEmpty : Test
  deleteFromEmpty
    = test "delete from empty map"
    $ let
      dmap : DMap K V
      dmap = empty
      in assertEq empty (delete kc2 dmap)

  deleteNonExistent : Test
  deleteNonExistent
    = test "delete a non-existent key"
    $ let
      dmap : DMap K V
      dmap = fromList [kvb0, kvb1, kvb2]
      in assertEq dmap (delete ka0 dmap)

  export
  tests : List Test
  tests
    = [ delete1
      , deleteFromEmpty
      , deleteNonExistent
      ]

namespace Union
  unionOfDisjointMaps : Test
  unionOfDisjointMaps
    = test "union of disjoint maps"
    $ let
      l1 = take 3 allPairs
      l2 = drop 3 allPairs
      in assertElems allPairs (fromList l1 `union` fromList l2)

  unionOfOverlappingMaps : Test
  unionOfOverlappingMaps
    = test "union of overlapping maps"
    $ let
      l1 = take 6 allPairs
      l2 = drop 3 allPairs
      in assertElems allPairs (fromList l1 `union` fromList l2)

  export
  tests : List Test
  tests = [unionOfDisjointMaps, unionOfOverlappingMaps]

namespace Difference

  submap : Test
  submap
    = test "subtract a submap"
    $ let
      dmap    = fromList allPairs
      subdmap = fromList (take 3 allPairs)
      in assertElems (drop 3 allPairs) (difference dmap subdmap)

  overlapping : Test
  overlapping
    = test "subtract an overlapping map"
    $ let
      dmap        = fromList (drop 3 allPairs)
      overlapping = fromList (take 6 allPairs)
      in assertElems (drop 6 allPairs) (difference dmap overlapping)

  disjoint : Test
  disjoint
    = test "subtract a disjoint map"
    $ let
      elems    = drop 6 allPairs
      dmap     = fromList elems
      disjoint = fromList (take 3 allPairs)
      in assertElems elems (difference dmap disjoint)


  export
  tests : List Test
  tests
    = [ submap
      , overlapping
      , disjoint
      ]

namespace Intersection

  submap : Test
  submap
    = test "intersection of a map with its submap"
    $ let
      elems = take 3 allPairs
      dmap    = fromList allPairs
      subdmap = fromList elems
      in assertElems elems (intersection dmap subdmap)

  overlapping : Test
  overlapping
    = test "intersection of overlapping maps"
    $ let
      dmap1 = fromList (take 6 allPairs)
      dmap2 = fromList (drop 3 allPairs)
      in assertElems (drop 3 $ take 6 allPairs) (intersection dmap1 dmap2)

  disjoint : Test
  disjoint
    = test "intersection of disjoint maps"
    $ let
      dmap1 = fromList (take 3 allPairs)
      dmap2 = fromList (drop 6 allPairs)
      in assertElems [] (intersection dmap1 dmap2)

  export
  tests : List Test
  tests
    = [ submap
      , overlapping
      , disjoint
      ]

allTests : List Test
allTests
   = FromList.tests
  ++ Eq.tests
  ++ Insert.tests
  ++ Lookup.tests
  ++ Delete.tests
  ++ Union.tests
  ++ Difference.tests
  ++ Intersection.tests

export
main : IO ()
main = do
  putStrLn "Testing `Data.DMap`"
  success <- runTests allTests
  pure ()
