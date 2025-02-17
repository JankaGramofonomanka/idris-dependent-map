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
%hide Data.List.lookup

%language ElabReflection

data K : Nat -> Type where
  MkK : Char -> (n : Nat) -> K n

%runElab derive "K" [Show]

V : Nat -> Type
V n = Vect n Char

param : DSum K V -> Nat
param (MkK _ n :=> _) = n

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

implementation [keyWise] Eq (DSum K V) where
  (k :=> _) == (k' :=> _) = deq' {f = K} k k'

implementation [paramWise] Eq (DSum K V) where
  (MkK _ n :=> _) == (MkK _ n' :=> _) = n == n'

--nubKeyWise : List (DSum K V) -> List (DSum K V)
--nubKeyWise kvs = nub kvs @{keyWise}

genParam : Gen Nat
genParam = nat (linear 0 10)

genNat : Gen Nat
genNat = nat (constant 0 100)

genK : (n : Nat) -> Gen (K n)
genK n = (\ch => MkK ch n) <$> alphaNum

genSomeK : Gen (Some K)
genSomeK = do
  n <- genParam
  k <- genK n
  pure (MkSome k)

genV : (n : Nat) -> Gen (V n)
genV n = vect n alphaNum

genKV : Gen (DSum K V)
genKV = do
  n <- genParam
  (:=>) <$> genK n <*> genV n

defaultRange : Range Nat
defaultRange = linear 0 100

genKVs : Gen (List (DSum K V))
genKVs = list defaultRange genKV

genKVsUniqueKeys : Gen (List (DSum K V))
genKVsUniqueKeys = nub @{keyWise} <$> genKVs

genKVsUniquePairs : Gen (List (DSum K V))
genKVsUniquePairs = nub <$> genKVs

genKVsNonEmpty : Gen (List (DSum K V))
genKVsNonEmpty = toList <$> list1 defaultRange genKV

genKVsUniqueKeysNonEmpty : Gen (List1 (DSum K V))
genKVsUniqueKeysNonEmpty = do
  kv ::: kvs <- list1 defaultRange genKV
  let kvs' = (nub kvs @{keyWise} \\ [kv]) @{keyWise}
  pure (kv ::: kvs)

theGenDMap : DOrd k => Hedgehog.Range Nat -> Gen (DSum k v) -> Gen (DMap k v)
theGenDMap range gen = fromList <$> list range gen

genDMap : Gen (DMap K V)
genDMap = theGenDMap defaultRange genKV

elemOf : Eq a => Show a => a -> List a -> PropertyT ()
elemOf x xs = diff x elem xs

-- TODO this is inefficient
shuffle : List Nat -> List a -> List a
shuffle ns xs = go (length xs) ns xs where
  go : Nat -> List Nat -> List a -> List a
  go len Nil xs = xs
  go len (n :: ns) xs = let
    pre  = take (n `mod` len) xs
    post = drop (n `mod` len) xs
    in go len ns (post ++ pre)

--||| Assert that the elements of the list are exactly the elements of the map
--||| @ elems the list
--||| @ dmap  the map
--assertAllElems : (elems : List (DSum K V)) -> (dmap : DMap K V) -> PropertyT ()
--assertAllElems elems dmap = sort elems === sort (toList dmap)

assertElem : (elem : DSum K V) -> (dmap : DMap K V) -> PropertyT ()
assertElem (k :=> v) dmap = lookup k dmap === Just v

assertElem' : (elem : DSum K V) -> (dmap : DMap K V) -> PropertyT ()
assertElem' kv dmap = kv `elemOf` toList dmap

assertNotElem : (k : K n) -> (dmap : DMap K V) -> PropertyT ()
assertNotElem k dmap = lookup k dmap === Nothing

sameElems : DMap K V -> DMap K V -> PropertyT ()
sameElems dmap dmap' = toList dmap === toList dmap'

namespace ToList

  -- This should pretty much ensure that both `toList` and `fromList` work correctly.
  -- At least that they preserve all information that a map shaould have.
  preservesInfo : Property
  preservesInfo = property $ do
    kvs <- forAll genKVs
    DMap.toList (fromList kvs) === sort (nub kvs @{keyWise})

namespace FromList

  orderInsensitive : Property
  orderInsensitive
    --= test "`fromList l == fromList (shuffle l)`"
    = property $ do
      [kvs, ns] <- forAll $ np [genKVsUniqueKeys, list defaultRange genNat]
      DMap.fromList kvs `sameElems` fromList (shuffle ns kvs)

  precedence : Property
  precedence = property $ do
    n <- forAll genParam
    [k, v1, v2, kvs1, kvs2, kvs3] <- forAll $ np [genK n, genV n, genV n, genKVs, genKVs, genKVs]

    -- TODO is this overengineered?
    let lhs, rhs : DMap K V
        lhs = DMap.fromList $ kvs1 ++ [k :=> v1] ++ kvs2 ++ [k :=> v2] ++ kvs3 --[k :=> v1, k :=> v2]
        rhs = DMap.fromList $ kvs1               ++ kvs2 ++ [k :=> v2] ++ kvs3 --[k :=> v2]

    lhs `sameElems` rhs

  --export
  --tests : List Test
  --tests = [fromEmpty, fromSingleton, fromAllPairs]

namespace Eq
  reflexive : Property
  reflexive
    -- = test "`dmap == dmap`"
    = property $ do
      dmap <- forAll genDMap
      dmap === dmap

  commutative : Property
  commutative
    = property $ do
      [dmap, dmap'] <- forAll $ np [genDMap, genDMap]
      (dmap == dmap') === (dmap' == dmap)

  differentElems : Property
  differentElems
    -- = test "maps constructed from different elements are not equal"
    = property $ do
        [nn, kvs, kvs'] <- forAll $ np [genNat, nub <$> genKVsNonEmpty, genKVs]

        let n = nn `mod` length kvs
            common = (kvs' \\ kvs) @{keyWise}
            lhs = DMap.fromList (take n kvs ++ common)
            rhs = DMap.fromList (drop n kvs ++ common)

        classify "no elements are the same" $ common == []
        --classify "(invalid) n > length kvs" $ n > length kvs
        classify "(invalid) lhs == rhs"     $ kvs    == []

        lhs /== rhs

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
      [kv@(k :=> v), kvs] <- forAll $ np [genKV, genKVs]

      classify "contains `k`"
        $ any ((==) kv @{keyWise})   kvs
      classify "contains pairs with the same parameter"
        $ any ((==) kv @{paramWise}) kvs
      classify "empty"
        $ kvs == []

      assertElem' kv (insert k v $ fromList kvs)

  insertTheSamPairTwice : Property
  insertTheSamPairTwice
    -- = test "insert the same pair twice"
    = property $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      let dmap'  = insert k v dmap
      let dmap'' = insert k v dmap'

      --size dmap' === size dmap''
      dmap' === dmap''

  insertTheSameKeyTwice : Property
  insertTheSameKeyTwice
    -- = test "insert 2 pairs with the same key"
    = property $ do
      [n, dmap]   <- forAll $ np [genParam, genDMap]
      [k, v1, v2] <- forAll $ np [genK n, genV n, genV n]

      let dmap'  = insert k v2 dmap
          dmap'' = insert k v1 dmap'

      size dmap' === size dmap''


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

  lookupInserted : Property
  lookupInserted
    -- = test "lookup in any map"
    = property $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      lookup k (insert k v dmap) === Just v

  lookupExistent : Property
  lookupExistent
    -- = test "lookup in any map"
    = property $ do
      [kv@(k :=> _), kvs, kvs'] <- forAll $ np [genKV, genKVs, genKVs]
      let dmap = DMap.fromList (kvs ++ [kv] ++ kvs)

      assert (isJust $ lookup k dmap)

  lookupNonExistent : Property
  lookupNonExistent
    -- = test "lookup a non-existent key"
    = property $ do
      (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
      lookup k (fromList kvs) === Nothing

  --export
  --tests : List Test
  --tests
  --  = [ lookupSingle
  --    , lookupIn9Elems
  --    , lookupEmpty
  --    , lookupNonExistent
  --    ]

namespace Delete

  -- NOT TRUE, see comment below
  -- TODO this is the same as `Lookup.lookupNonExistent`. What should I do about it?
  -- Maybe its a mistake to test the insert, delete, lookup functions separately,
  -- maybe I should treat them as a whole
  --
  -- Now that I rewrote `lookupNonExistent` to not use `delete` the above is no
  -- longer true but the reflexion is still valid
  delete1 : Property
  delete1
    -- = test "delete 1 element"
    = property $ do
        [MkSome k, dmap] <- forAll $ np [genSomeK, genDMap]
        lookup k (delete k dmap) === Nothing

  deleteNonExistent : Property
  deleteNonExistent
  --  = test "delete a non-existent key"
    = property $ do
        (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
        let dmap = DMap.fromList kvs

        dmap === delete k dmap

  deleteExistent : Property
  deleteExistent
  --  = test "delete an existent key"
    = property $ do
        (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
        let dmap = DMap.fromList kvs

        dmap === delete k (insert k v dmap)
  --export
  --tests : List Test
  --tests
  --  = [ delete1
  --    , deleteFromEmpty
  --    , deleteNonExistent
  --    ]

namespace Empty
  emptyToList : Property
  emptyToList = property $ DMap.toList (the (DMap K V) empty) === []

  fromEmpty : Property
  fromEmpty = property $ the (DMap K V) empty === fromList []
  --  = test "make a map from an empty list"

  lookupInEmpty : Property
  lookupInEmpty
    -- = test "lookup in empty map"
    = property $ do
      MkSome k <- forAll genSomeK
      let dmap = the (DMap K V) empty
      lookup k dmap === Nothing

  deleteFromEmpty : Property
  deleteFromEmpty
    -- = test "delete from empty map"
    = property $ do
      MkSome k <- forAll genSomeK
      let dmap = the (DMap K V) empty
      dmap === (delete k dmap)

namespace Singleton
  singletonToList : Property
  singletonToList = property $ do
    k :=> v <- forAll genKV
    DMap.toList (the (DMap K V) (singleton k v)) === [k :=> v]

  fromSingleton : Property
  fromSingleton = property $ do
    --  = test "make a map from singleton list"
    kv@(k :=> v) <- forAll genKV
    singleton k v === fromList [kv]

  lookupInSingleton : Property
  lookupInSingleton
    -- = test "`lookup` in sinlgetom"
    = property $ do
      k :=> v <- forAll genKV
      let dmap = the (DMap K V) (singleton k v)
      lookup k dmap === Just v

  insertToEmpty : Property
  insertToEmpty
    = property $ do
      k :=> v <- forAll genKV
      let lhs, rhs : DMap K V
          lhs = singleton k v
          rhs = insert k v empty
      lhs === rhs

namespace Union

  union : Property
  union = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `union` fromList kvs2) === fromList (kvs1 ++ kvs2)

  idempotent : Property
  idempotent = property $ do
    dmap <- forAll genDMap
    (dmap `union` dmap) === dmap

  unionPrecedence : Property
  unionPrecedence = property $ do
    n <- forAll genParam
    [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

    assertElem (k :=> v1) (insert k v1 dmap1 `union` insert k v2 dmap2) -- TODO or is it v2?

  unionWithSubmap : Property
  unionWithSubmap = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]
    let supermap = insert k v dmap
    (dmap `union` supermap) === supermap

  unionWithOverlapping : Property
  unionWithOverlapping = property $ do
    [k1 :=> v1, k2 :=> v2, dmap] <- forAll $ np [genKV, genKV, genDMap]
    (insert k1 v1 dmap `union` insert k2 v2 dmap) === (insert k1 v1 . insert k2 v2 $ dmap)

  associativity : Property
  associativity = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    ((a `union` b) `union` c) === (a `union` (b `union` c))

  identity : Property
  identity = property $ do
    a <- forAll genDMap
    (a `union` empty) === a


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

  nilpotent : Property
  nilpotent = property $ do
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

  -- TODO precedence?
  commutative : Property
  commutative = property $ do
    [dmap1, dmap2] <- forAll $ np [genDMap, genDMap]
    (dmap1 `intersection` dmap2) === (dmap2 `intersection` dmap1)

  idempotent : Property
  idempotent = property $ do
    dmap <- forAll genDMap
    (dmap `intersection` dmap) === dmap

  intersectionWithSubmap : Property
  intersectionWithSubmap = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]
    (insert k v dmap `intersection` dmap) === dmap

  intersectionPrecedence : Property
  intersectionPrecedence = property $ do
    n <- forAll genParam
    [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

    assertElem (k :=> v1) (insert k v1 dmap1 `intersection` insert k v2 dmap2)

  associativity : Property
  associativity = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    ((a `intersection` b) `intersection` c) === (a `intersection` (b `intersection` c))

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
-}

namespace Size

  prop1 : Property
  prop1 = property $ do
    xs <- forAll genKVs
    DMap.size (DMap.fromList xs) === cast (length (nub xs @{keyWise}))

-- union a b = (a `difference` b) `union` (a `intersection` b) `union` (b `difference` a)
-- a === (a `difference` b) `union` (a `intersection` b)
-- a `difference` (a `difference`   b) === (a `intersection` b)
-- a `difference` (a `intersection` b) === (a `difference`   b)
-- a `difference` (a `intersection` b) `difference` (a `difference` b) === empty

prop1, prop2, prop3, prop4 : Property
prop1 = property $ do
  [a, b] <- forAll $ np [genDMap, genDMap]
  let lhs = union a b
      rhs = ((a `difference` b) `union` (a `intersection` b)) `union` (b `difference` a)
  lhs === rhs

prop2 = property $ do
  [a, b] <- forAll $ np [genDMap, genDMap]
  (a `difference` (a `difference`   b)) === (a `intersection` b)

prop3 = property $ do
  [a, b] <- forAll $ np [genDMap, genDMap]
  (a `difference` (a `intersection` b)) === (a `difference`   b)

prop4 = property $ do
  [a, b] <- forAll $ np [genDMap, genDMap]
  ((a `difference` (a `intersection` b)) `difference` (a `difference` b)) === empty

distributive1, distributive2 : Property
distributive1 = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    (a `union` (b `intersection` c)) === ((a `union` b) `intersection` (a `union` c))

distributive2 = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    (a `intersection` (b `union` c)) === ((a `intersection` b) `union` (a `intersection` c))

absorption1, absorption2 : Property
absorption1 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    (a `union` (a `intersection` b)) === a

absorption2 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    (a `intersection` (a `union` b)) === a

{-
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
