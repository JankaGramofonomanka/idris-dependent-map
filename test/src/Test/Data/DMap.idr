module Test.Data.DMap

import Data.List
import Data.Singleton
import Data.Vect
import Derive.Prelude

--import Tester
--import Tester.Runner

import Data.DMap as TheDMap
--import Data.DMapGen
import Data.DSum
import Data.DEq
import Data.DOrd

import Data.SOP
import Hedgehog

%hide Oh
%hide Prelude.Range

%language ElabReflection

data K : Nat -> Type where
  MkK : Char -> (n : Nat) -> K n

%runElab derive "K" [Show]

V : Nat -> Type
V n = Vect n Char

unsafeDEQ : DOrdering a b
unsafeDEQ = believe_me $ the (DOrdering 0 0) DEQ

unsafeBoolToMEq : Bool -> Maybe (a = b)
unsafeBoolToMEq True = Just (believe_me $ the (0 = 0) Refl)
unsafeBoolToMEq False = Nothing

unsafeOrderingToGOrdering : Ordering -> DOrdering a b
unsafeOrderingToGOrdering LT = DLT
unsafeOrderingToGOrdering EQ = unsafeDEQ
unsafeOrderingToGOrdering GT = DGT

implementation DEq K where
  deq (MkK i1 a) (MkK i2 b) = unsafeBoolToMEq ((i1, a) == (i2, b))

implementation DEq V where
  deq xs ys = unsafeBoolToMEq (toList xs == toList ys)

implementation DOrd K where
  dcompare (MkK i1 a) (MkK i2 b) = unsafeOrderingToGOrdering (compare (i1, a) (i2, b))

implementation DOrd V where
  dcompare xs ys = unsafeOrderingToGOrdering (compare (toList xs) (toList ys))

implementation DShow K where
  dshow k = show k

implementation DShow V where
  dshow v = show v

genNat : Gen Nat
genNat = nat (linear 0 10)

genK : (n : Nat) -> Gen (K n)
genK n = (\ch => MkK ch n) <$> alphaNum

genSomeK : Gen (Some K)
genSomeK = do
  n <- genNat
  k <- genK n
  pure (MkSome k)

genV : (n : Nat) -> Gen (V n)
genV n = vect n alphaNum

genKV : Gen (DSum K V)
genKV = do
  n <- genNat
  (:=>) <$> genK n <*> genV n

defaultRange : Range Nat
defaultRange = linear 0 100

genKVs : Gen (List (DSum K V))
genKVs = list defaultRange genKV

theGenDMap : DOrd k => Hedgehog.Range Nat -> Gen (DSum k v) -> Gen (DMap k v)
theGenDMap range gen = fromList <$> list range gen

genDMap : Gen (DMap K V)
genDMap = theGenDMap defaultRange genKV


||| Assert that the elements of the list are exactly the elements of the map
||| @ elems the list
||| @ dmap  the map
assertAllElems : (elems : List (DSum K V)) -> (dmap : DMap K V) -> PropertyT ()
assertAllElems elems dmap = sort elems === sort (toList dmap)

assertElem : (elem : DSum K V) -> (dmap : DMap K V) -> PropertyT ()
assertElem (k :=> v) dmap = lookup k dmap === Just v

assertNotElem : (k : K n) -> (dmap : DMap K V) -> PropertyT ()
assertNotElem k dmap = lookup k dmap === Nothing

namespace FromList

  fromEmpty : Property
  fromEmpty = property $ the (DMap K V) empty === fromList []
  --  = test "make a map from an empty list"

  fromSingleton : Property
  fromSingleton = property $ do
    --  = test "make a map from singleton list"
    kv@(k :=> v) <- forAll genKV
    singleton k v === fromList [kv]

  fromMultiple : Property
  fromMultiple = property $ do
    --  = test "make a map from a multi-element list"
    kvs <- forAll $ list defaultRange genKV
    assertAllElems kvs (fromList kvs)

  prop1 : Property
  prop1 = property $ do
    kvs <- forAll genKVs
    DMap.fromList kvs === DMap.fromList (nub kvs)

  --export
  --tests : List Test
  --tests = [fromEmpty, fromSingleton, fromAllPairs]

namespace Eq
  -- REMOVE this should be covered by the next one
  reflexiveEmpty : Property
  reflexiveEmpty
    -- = test "`empty == empty`"
    = let
      dmap : DMap K V
      dmap = empty
      in property $ dmap === dmap

  reflexiveNonEmpty : Property
  reflexiveNonEmpty
    -- = test "`dmap == dmap`"
    = property $ do
      dmap <- forAll genDMap
      dmap === dmap

  reversedEqualsItself : Property
  reversedEqualsItself
    --= test "`fromList l == fromList (reverse l)`"
    = property $ do
      l <- forAll $ list defaultRange genKV
      DMap.fromList l === fromList (reverse l)

  emptyNonEmpty : Property
  emptyNonEmpty
    -- = test "`empty /= dmap` where `dmap` is non-empty"
    = property $ do
      kvs <- forAll $ toList <$> list1 defaultRange genKV
      let dmap = fromList kvs
      DMap.empty /== dmap

  --differentElems : Test
  --differentElems
  --  = test "maps constructed from different elements are not equal"
  --  $ let
  --    lhs = DMap.fromList (take 3 allPairs)
  --    rhs = DMap.fromList (drop 6 allPairs)
  --    in assertNotEq lhs rhs

  --export
  --tests : List Test
  --tests
  --  = [ reflexiveEmpty
  --    , reflexiveNonEmpty
  --    , reversedEqualsItself
  --    , emptyNonEmpty
  --    , differentElems
  --    ]

namespace Insert
  insert1 : Property
  insert1
    -- = test "insert 1 element"
    = property $ do
      kv@(k :=> v) <- forAll genKV
      dmap <- forAll genDMap
      assertElem kv (insert k v dmap)

  insert2Different : Property
  insert2Different
    -- = test "insert 2 pairs with different parameter"
    = property $ do
      [k1 :=> v1, k2 :=> v2, dmap] <- forAll $ np [genKV, genKV, genDMap]

      -- TODO assiuming kv1 /= kv2
      let dmap' = insert k2 v2
                . insert k1 v1
                $ dmap
      assertElem (k1 :=> v1) dmap' -- && assertElem [k2 :=> v2] dmap' TODO

  insert2Same : Property
  insert2Same
    -- = test "insert 2 pairs with the same parameter"
    = property $ do
      [n, dmap]        <- forAll $ np [genNat, genDMap]
      [k1, k2, v1, v2] <- forAll $ np [genK n, genK n, genV n, genV n]

      -- TODO assiuming kv1 /= kv2
      classify "keys equal - test meaningless"     (      deq' {f = K} k1 k2)
      classify "keys not equal - test meaningfull" (not $ deq' {f = K} k1 k2)

      let dmap' = insert k2 v2
                . insert k1 v1
                $ dmap
      assertElem (k1 :=> v1) dmap' -- && assertElem [k2 :=> v2] dmap' TODO

  insertTheSamPairTwice : Property
  insertTheSamPairTwice
    -- = test "insert the same pair twice"
    = property $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      let dmap'  = insert k v dmap
      let dmap'' = insert k v dmap'

      size dmap' === size dmap''

  insertTheSameKeyTwice : Property
  insertTheSameKeyTwice
    -- = test "insert 2 pairs with the same key"
    = property $ do
      [n, dmap]   <- forAll $ np [genNat, genDMap]
      [k, v1, v2] <- forAll $ np [genK n, genV n, genV n]

      let dmap' = insert k v2
                . insert k v1
                $ dmap
      assertElem (k :=> v2) dmap'

  {-
  insertAllPairs : Test
  insertAllPairs
    = test "insert multiple pairs"
    $ let
      dmap : DMap K V
      dmap = foldr (\(k :=> v) => insert k v) empty allPairs
    in assertAllElems allPairs dmap
  -}

  --export
  --tests : List Test
  --tests
  --  = [ insert1
  --    , insert2Different
  --    , insert2Same
  --    , insertTheSamPairTwice
  --    , insertTheSameKeyTwice
  --    , insertAllPairs
  --    ]

namespace Lookup
  lookupSingle : Property
  lookupSingle
    -- = test "`lookup` in sinlgetom"
    = property $ do
      k :=> v <- forAll genKV
      let dmap = the (DMap K V) (singleton k v)
      lookup k dmap === Just v

  lookupInMultipleElems : Property
  lookupInMultipleElems
    -- = test "lookup in a multi-element map"
    = property $ do
      [kv, kvs] <- forAll $ np [genKV, list defaultRange genKV]

      assertElem kv (fromList kvs)


  lookupEmpty : Property
  lookupEmpty
    -- = test "lookup in empty map"
    = property $ do
      n <- forAll genNat
      k <- forAll (genK n)
      let dmap = the (DMap K V) empty
      lookup k dmap === Nothing

  -- TODO assuning k is not in ks
  --lookupNonExistent : Test
  --lookupNonExistent
  --  = test "lookup a non-existent key"
  --  $ let
  --    dmap : DMap K V
  --    dmap = fromList [kvb0, kvb1, kvb2]
  --    in assertEq (lookup ka0 dmap) Nothing

  --export
  --tests : List Test
  --tests
  --  = [ lookupSingle
  --    , lookupIn9Elems
  --    , lookupEmpty
  --    , lookupNonExistent
  --    ]

namespace Delete
  delete1 : Property
  delete1
    -- = test "delete 1 element"
    = property $ do
        [MkSome k, dmap] <- forAll $ np [genSomeK, genDMap]
        assertNotElem k (delete k dmap)

  deleteFromEmpty : Property
  deleteFromEmpty
    -- = test "delete from empty map"
    = property $ do
      MkSome k <- forAll genSomeK
      let dmap = the (DMap K V) empty
      dmap === (delete k dmap)

  -- TODO assuming k is not in ks
  --deleteNonExistent : Test
  --deleteNonExistent
  --  = test "delete a non-existent key"
  --  $ let
  --    dmap : DMap K V
  --    dmap = fromList [kvb0, kvb1, kvb2]
  --    in assertEq dmap (delete ka0 dmap)

  --export
  --tests : List Test
  --tests
  --  = [ delete1
  --    , deleteFromEmpty
  --    , deleteNonExistent
  --    ]

namespace Union

  union : Property
  union = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `union` fromList kvs2) === fromList (kvs1 ++ kvs2)

  unionWithItself : Property
  unionWithItself = property $ do
    dmap <- forAll genDMap
    (dmap `union` dmap) === dmap

  unionPrecedence : Property
  unionPrecedence = property $ do
    n <- forAll genNat
    [k, v1, v2, dmap] <- forAll $ np [genK n, genV n, genV n, genDMap]

    assertElem (k :=> v1) (insert k v1 dmap `union` insert k v2 dmap) -- TODO or is it v2?

  unionWithSubmap : Property
  unionWithSubmap = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]
    let supermap = insert k v dmap
    (dmap `union` supermap) === supermap

  unionWithOverlapping : Property
  unionWithOverlapping = property $ do
    [k1 :=> v1, k2 :=> v2, dmap] <- forAll $ np [genKV, genKV, genDMap]
    (insert k1 v1 dmap `union` insert k2 v2 dmap) === (insert k1 v1 . insert k2 v2 $ dmap)

{-
  -- TODO assuming disjoint
  unionOfDisjointMaps : Test
  unionOfDisjointMaps
    = test "union of disjoint maps"
    $ let
      l1 = take 3 allPairs
      l2 = drop 3 allPairs
      in assertAllElems allPairs (fromList l1 `union` fromList l2)

  -- TODO assuming overlapping
  unionOfOverlappingMaps : Test
  unionOfOverlappingMaps
    = test "union of overlapping maps"
    $ let
      l1 = take 6 allPairs
      l2 = drop 3 allPairs
      in assertAllElems allPairs (fromList l1 `union` fromList l2)

  --export
  --tests : List Test
  --tests = [unionOfDisjointMaps, unionOfOverlappingMaps]
-}

namespace Difference

  difference : Property
  difference = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `difference` fromList kvs2) === fromList (kvs1 \\ kvs2)

  differenceBetweenItself : Property
  differenceBetweenItself = property $ do
    dmap <- forAll genDMap
    (dmap `difference` dmap) === empty

  differenceWithSubmap : Property
  differenceWithSubmap = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]
    let supermap = insert k v dmap
    (supermap `difference` dmap) === singleton k v
{-
  submap : Test
  submap
    = test "subtract a submap"
    $ let
      dmap    = fromList allPairs
      subdmap = fromList (take 3 allPairs)
      in assertAllElems (drop 3 allPairs) (difference dmap subdmap)

  overlapping : Test
  overlapping
    = test "subtract an overlapping map"
    $ let
      dmap        = fromList (drop 3 allPairs)
      overlapping = fromList (take 6 allPairs)
      in assertAllElems (drop 6 allPairs) (difference dmap overlapping)

  disjoint : Test
  disjoint
    = test "subtract a disjoint map"
    $ let
      elems    = drop 6 allPairs
      dmap     = fromList elems
      disjoint = fromList (take 3 allPairs)
      in assertAllElems elems (difference dmap disjoint)


  --export
  --tests : List Test
  --tests
  --  = [ submap
  --    , overlapping
  --    , disjoint
  --    ]
-}

namespace Intersection

  intersection : Property
  intersection = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `intersection` fromList kvs2) === fromList (kvs1 `intersect` kvs2)

  intersectionReflexive : Property
  intersectionReflexive = property $ do
    [dmap1, dmap2] <- forAll $ np [genDMap, genDMap]
    (dmap1 `intersection` dmap2) === (dmap2 `intersection` dmap1)

  intersectionWithItself : Property
  intersectionWithItself = property $ do
    dmap <- forAll genDMap
    (dmap `intersection` dmap) === dmap

  intersectionWithSubmap : Property
  intersectionWithSubmap = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]
    (insert k v dmap `intersection` dmap) === dmap

  intersectionPrecedence : Property
  intersectionPrecedence = property $ do
    n <- forAll genNat
    [k, v1, v2, dmap] <- forAll $ np [genK n, genV n, genV n, genDMap]

    (insert k v1 dmap `intersection` insert k v2 dmap) === insert k v1 dmap

{-
  submap : Test
  submap
    = test "intersection of a map with its submap"
    $ let
      elems = take 3 allPairs
      dmap    = fromList allPairs
      subdmap = fromList elems
      in assertAllElems elems (intersection dmap subdmap)

  overlapping : Test
  overlapping
    = test "intersection of overlapping maps"
    $ let
      dmap1 = fromList (take 6 allPairs)
      dmap2 = fromList (drop 3 allPairs)
      in assertAllElems (drop 3 $ take 6 allPairs) (intersection dmap1 dmap2)

  disjoint : Test
  disjoint
    = test "intersection of disjoint maps"
    $ let
      dmap1 = fromList (take 3 allPairs)
      dmap2 = fromList (drop 6 allPairs)
      in assertAllElems [] (intersection dmap1 dmap2)

  --export
  --tests : List Test
  --tests
  --  = [ submap
  --    , overlapping
  --    , disjoint
  --    ]

allTests : List Test
--allTests
--   = FromList.tests
--  ++ Eq.tests
--  ++ Insert.tests
--  ++ Lookup.tests
--  ++ Delete.tests
--  ++ Union.tests
--  ++ Difference.tests
--  ++ Intersection.tests

export
main : IO ()
main = do
  putStrLn "Testing `Data.DMap`"
  True <- runTests allTests
        | False => assert_total (idris_crash "tests failed")
  pure ()

-}
