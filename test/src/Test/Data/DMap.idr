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
%hide Data.List.union

%language ElabReflection

describe : PropertyName -> Property -> (PropertyName, Property)
describe n p = (n, p)

data K : Nat -> Type where
  MkK : String -> (n : Nat) -> K n

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

||| remove all occurances of an element
deleteAll : Eq a => a -> List a -> List a
deleteAll _ []      = []
deleteAll x (y::ys) = (if x == y then [] else [y]) ++ deleteAll x ys

export infix 7 \\\
||| delete all occurances of each element from the right list, in the left list
(\\\) : Eq a => List a -> List a -> List a
(\\\) = foldl (flip deleteAll)


-- TODO this is inefficient
shuffle : List Nat -> List a -> List a
shuffle ns Nil = Nil
shuffle ns xs = go (length xs) ns xs where
  go : Nat -> List Nat -> List a -> List a
  go len Nil xs = xs
  go len (n :: ns) xs = let
    pre  = take (n `mod` len) xs
    post = drop (n `mod` len) xs
    in go len ns (post ++ pre)

sortVect : Ord a => Vect n a -> Vect n a
sortVect xs = believe_me (sort {a} (believe_me xs))

slice1 : Nat -> List a -> (List a, List a)
slice1 n l = let n' = n `mod` length l in (take n' l, drop n' l)

slice : Vect n Nat -> List a -> Vect (S n) (List a)
slice ns Nil = [] :: map (const []) ns
slice ns l = go 0 (massage ns) l where

  massage : Vect k Nat -> Vect k Nat
  massage = sortVect . map (`mod` length l)
  --massage Vect
  go : Nat -> Vect m Nat -> List a -> Vect (S m) (List a)
  go prevN Nil l = [l]
  go prevN (n :: ns) l = let
    (pre, post) = slice1 (n `minus` prevN) l
    in pre :: go n ns post

defaultRange : Range Nat
defaultRange = linear 0 100

genParam : Gen Nat
genParam = nat (linear 0 10)

genNat : Gen Nat
genNat = nat (constant 0 100)

genK : (n : Nat) -> Gen (K n)
genK n = (\s => MkK s n) <$> string defaultRange alphaNum

genSomeK : Gen (Some K)
genSomeK = do
  [s, n] <- np [string defaultRange alphaNum, genParam]
  pure (MkSome $ MkK s n)

genV : (n : Nat) -> Gen (V n)
genV n = vect n alphaNum

genKV : Gen (DSum K V)
genKV = do
  n <- genParam
  (:=>) <$> genK n <*> genV n

genKVs : Gen (List (DSum K V))
genKVs = list defaultRange genKV

--genKVsUnique : Eq (DSum K V) => Gen (List (DSum K V))
--genKVsUnique = nub <$> genKVs

genKVsUniqueKeys : Gen (List (DSum K V))
genKVsUniqueKeys = nub @{keyWise} <$> genKVs
--genKVsUniqueKeys = genKVsUnique @{keyWise}

genKVsUniquePairs : Gen (List (DSum K V))
genKVsUniquePairs = nub <$> genKVs
--genKVsUniquePairs = genKVsUnique

genKVsNonEmpty : Gen (List (DSum K V))
genKVsNonEmpty = toList <$> list1 defaultRange genKV

genKVsUniqueNonEmpty : (impl : Eq (DSum K V)) => Gen (List1 (DSum K V))
genKVsUniqueNonEmpty = do
  kv ::: kvs <- list1 defaultRange genKV
  let kvs' = (nub kvs @{impl} \\ [kv]) @{impl}
  pure (kv ::: kvs')

genKVsUniqueKeysNonEmpty : Gen (List1 (DSum K V))
genKVsUniqueKeysNonEmpty = genKVsUniqueNonEmpty @{keyWise}

genKVsUniquePairsNonEmpty : Gen (List1 (DSum K V))
genKVsUniquePairsNonEmpty = genKVsUniqueNonEmpty

genKVsDisjoint : (n : Nat) -> Gen (List (DSum K V)) -> Gen (Vect n (List (DSum K V)))
genKVsDisjoint Z gen = pure []
genKVsDisjoint (S n) gen = do
  [kvs, ns] <- np [gen, vect n genNat]
  pure (slice ns kvs)

-- disjoint in the key comparison sense
genKVsConsistentDisjoint : (n : Nat) -> Gen (Vect n (List (DSum K V)))
genKVsConsistentDisjoint n = genKVsDisjoint n genKVsUniqueKeys

-- when a key is in both lists, the value is the same
genKVsConsistentOverlapping : Gen (Vect 2 (List (DSum K V)))
genKVsConsistentOverlapping = do
  [common, kvs1, kvs2] <- genKVsConsistentDisjoint 3
  pure [common ++ kvs1, common ++ kvs2]

theGenDMap : DOrd k => Hedgehog.Range Nat -> Gen (DSum k v) -> Gen (DMap k v)
theGenDMap range gen = fromList <$> list range gen

genDMap : Gen (DMap K V)
genDMap = theGenDMap defaultRange genKV

-- when a key is in both maps, the value is the same
genDMapsConsistent : Gen (Vect 2 (DMap K V))
genDMapsConsistent = map fromList <$> genKVsConsistentOverlapping

-- disjoint in the key comparison sense
genDMapsConsistentDisjoint : (n : Nat) -> Gen (Vect n (DMap K V))
genDMapsConsistentDisjoint n = map fromList <$> genKVsConsistentDisjoint n

elemOf : Eq a => Show a => a -> List a -> PropertyT ()
elemOf x xs = diff x elem xs

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

namespace ToListFromList

  -- This should pretty much ensure that both `toList` and `fromList` work correctly.
  -- At least that they preserve all information that a map shaould have.
  preservesInfo : Property
  preservesInfo = property $ do
    kvs <- forAll genKVs
    -- reverse `kvs` so that the last key stays in the `nubbed` list
    DMap.toList (fromList kvs) === sort (nub (reverse kvs) @{keyWise})

  export
  toListFromListProps : Group
  toListFromListProps
    = MkGroup "properties regarding `toList` and `fromList`"
    $ [ describe "`toList` and `fromList` preserve the information contained in a map" preservesInfo
      ]

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

  export
  fromListProps : Group
  fromListProps
    = MkGroup "`fromList` properties"
    $ [ describe "`fromList` is insensitive to order of lists with unique keys" orderInsensitive
      , describe "test precedence of list elements"                             precedence
      ]
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
        [nn, kvs, kvs'] <- forAll $ np [genNat, toList <$> genKVsUniquePairsNonEmpty, genKVs]

        let n = nn `mod` length kvs
            common = (kvs' \\\ kvs) @{keyWise}
            lhs = DMap.fromList (take n kvs ++ common)
            rhs = DMap.fromList (drop n kvs ++ common)
        --[common, kvs1, kvs2] <- forAll $ genKVsDisjoint3 genKVsUniquePairs
        --let lhs = DMap.fromList (common ++ kvs1)
        --    rhs = DMap.fromList (common ++ kvs2)

        classify "no elements are the same" $ common == []
        --classify "(invalid) n > length kvs" $ n > length kvs
        classify "(invalid) lhs == rhs"     $ kvs    == []
        --classify "(invalid) lhs == rhs"     $ kvs1   == kvs2

        lhs /== rhs

  export
  eqProps : Group
  eqProps
    = MkGroup "`Eq` implementation properties"
    $ [ describe "(==) is reflexive"                          reflexive
      , describe "(==) is commutative"                        commutative
      , describe "maps with different elemetns are not equal" differentElems
      ]

  --export
  --tests : List Test
  --tests
  --  = [ reflexiveEmpty
  --    , reflexiveNonEmpty
  --    , reversedEqualsItself
  --    , emptyNonEmpty
  --    , differentElems
  --    ]

namespace Lookup

  lookupExistent : Property
  lookupExistent
    -- = test "lookup in any map"
    = property $ do
      [kv@(k :=> _), kvs, kvs'] <- forAll $ np [genKV, genKVs, genKVs]
      let dmap = DMap.fromList (kvs ++ [kv] ++ kvs)

      assert (isJust $ lookup k dmap)

  export
  lookupNonExistent : Property
  lookupNonExistent
    -- = test "lookup a non-existent key"
    = property $ do
      (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
      lookup k (fromList kvs) === Nothing

  export
  lookupProps : Group
  lookupProps
    = MkGroup "`lookup` properties"
    $ [ describe "lookup of an existent key is successful"      lookupExistent
      , describe "lookup of a non-existent key is unsuccessful" lookupNonExistent
      ]

  --export
  --tests : List Test
  --tests
  --  = [ lookupSingle
  --    , lookupIn9Elems
  --    , lookupEmpty
  --    , lookupNonExistent
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

      lookup k (insert k v $ fromList kvs) === Just v

  insert2 : Property
  insert2
    -- = test "insert 2 elements"
    = property $ do
      [kv1@(k1 :=> v1), kv2@(k2 :=> v2), dmap] <- forAll $ np [genKV, genKV, genDMap]

      classify "keys are the same" (deq' k1 k2 {f = K})

      lookup k2 (insert k2 v2 . insert k1 v1 $ dmap) === Just v2

  insertTheSamPairTwice : Property
  insertTheSamPairTwice
    -- = test "insert the same pair twice"
    = property $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      let dmap'  = insert k v dmap
      let dmap'' = insert k v dmap'

      --size dmap' === size dmap''
      dmap' === dmap''

  export
  insertProps : Group
  insertProps
    = MkGroup "`insert` properties"
    $ [ describe "lookup of an inserted element is successful"                     insert1
      , describe "after inserting 2 pairs, lookup of the second key is successful" insert2
      , describe "inserting a pair the second time is uneffectful"                 insertTheSamPairTwice
      ]

  -- should be covered by `insert2`
  --insertTheSameKeyTwice : Property
  --insertTheSameKeyTwice
  --  -- = test "insert 2 pairs with the same key"
  --  = property $ do
  --    [n, dmap]   <- forAll $ np [genParam, genDMap]
  --    [k, v1, v2] <- forAll $ np [genK n, genV n, genV n]
  --
  --    lookup k (insert k v2 . insert k v1 $ dmap) === Just v2


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

namespace Delete

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

  export
  deleteProps : Group
  deleteProps
    = MkGroup "`delete` properties"
    $ [ describe "lookup of a deleted element is ubsuccesful"        delete1
      , describe "deletion of a non-existent element is uneffectful" deleteNonExistent
      , describe "test deletion of an existing key"                  deleteExistent
      ]

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

  export
  emptyProps : Group
  emptyProps
    = MkGroup "`empty` properties"
    $ [ describe "empty converted to a list is the empty list"    emptyToList
      , describe "empty is a map constructed from the empty list" fromEmpty
      , describe "lookup in empty is unsuccessful"                lookupInEmpty
      , describe "deletion from empty is uneffectful"             deleteFromEmpty
      ]

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

  export
  singletonProps : Group
  singletonProps
    = MkGroup "`singleton` properties"
    $ [ describe "singleton converted to a list is a singleton list"    singletonToList
      , describe "singleton is a map constructed from a singleton list" fromSingleton
      , describe "lookup in singleton is successful"                    lookupInSingleton
      , describe "inserting to empty returns a singleton"               insertToEmpty
      ]

namespace Size

  definition : Property
  definition = property $ do
    xs <- forAll genKVs
    DMap.size (DMap.fromList xs) === cast {from = Nat, to = Int} (length (nub xs @{keyWise}))

  propDelete : Property
  propDelete = property $ do
    [MkSome k, dmap] <- forAll $ np [genSomeK, genDMap]

    classify "k present"     (isJust    $ lookup k dmap)
    classify "k not present" (isNothing $ lookup k dmap)

    case lookup k dmap of
      Nothing => size dmap === size (delete k dmap)
      Just _  => size dmap === size (delete k dmap) + 1

  propInsert : Property
  propInsert = property $ do
    [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

    classify "k present"     (isJust    $ lookup k dmap)
    classify "k not present" (isNothing $ lookup k dmap)

    case lookup k dmap of
      Nothing => size (insert k v dmap) === size dmap + 1
      Just _  => size (insert k v dmap) === size dmap

  -- TODO redundant (`propInsertMultiple`), but simpler
  propInsertTwice : Property
  propInsertTwice = property $ do
    n <- forAll genParam
    [k, v1, v2, dmap] <- forAll $ np [genK n, genV n, genV n, genDMap]

    let dmap'  = insert k v1 dmap
        dmap'' = insert k v2 dmap'

    size dmap' === size dmap''

  propInsertMultiple : Property
  propInsertMultiple = property $ do
    [n, m, dmap] <- forAll $ np [genParam, genNat, genDMap]
    [k, v :: vs] <- forAll $ np [genK n, vect (S $ S m) (genV n)]

    let dmap'  = insert k v dmap
        dmap'' = foldr (insert k) dmap' vs

    size dmap' === size dmap''

  export
  sizeProps : Group
  sizeProps
    = MkGroup "`size` properties"
    $ [ describe "test against the definition"                           definition
      , describe "size change after deletion"                            propDelete
      , describe "size change after insertion"                           propInsert
      , describe "size change after two insertions to the same key"      propInsertTwice
      , describe "size change after multiple insertions to the same key" propInsertMultiple
      ]

namespace Union

  definition : Property
  definition = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs2 `union` fromList kvs1) === fromList (kvs1 ++ kvs2)

  precedence : Property
  precedence = property $ do
    n <- forAll genParam
    [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

    lookup k (insert k v1 dmap1 `union` insert k v2 dmap2) === Just v1

  unionWithSubmap : Property
  unionWithSubmap = property $ do
    [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
    let submap   = fromList kvs2
    let supermap = fromList (kvs1 ++ kvs2)
    (supermap `union` submap) === supermap

  unionWithOverlapping : Property
  unionWithOverlapping = property $ do
    --[k1 :=> v1, k2 :=> v2, dmap] <- forAll $ np [genKV, genKV, genDMap]
    --(insert k1 v1 dmap `union` insert k2 v2 dmap) === (insert k1 v1 . insert k2 v2 $ dmap)
    --[kvs, kvs', kvs''] <- forAll $ np [genKVs, genKVs, genKVs]
    --(fromList (kvs ++ kvs'') `union` fromList (kvs ++ kvs')) === fromList (kvs ++ kvs' ++ kvs'')
    --[kvs, n1, n2] <- forAll $ np [genKVsUniqueKeys, genNat, genNat]
    --let [common, kvs1, kvs2] = slice [n1, n2] kvs
    [common, kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 3)
    let lhs = fromList (common ++ kvs2) `union` fromList (common ++ kvs1)
        rhs = fromList (common ++ kvs1 ++ kvs2)

    lhs === rhs

  identity : Property
  identity = property $ do
    a <- forAll genDMap
    (a `union` empty) === a

  idempotent : Property
  idempotent = property $ do
    dmap <- forAll genDMap
    (dmap `union` dmap) === dmap

  associative : Property
  associative = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    ((a `union` b) `union` c) === (a `union` (b `union` c))

  commutative : Property
  commutative = property $ do
    [dmap1, dmap2] <- forAll genDMapsConsistent
    (dmap1 `union` dmap2) === (dmap2 `union` dmap1)

  export
  unionProps : Group
  unionProps
    = MkGroup "`union` properties"
    $ [ describe "test against the definition"       definition
      , describe "test precedence"                   precedence
      , describe "union with submap is the supermap" unionWithSubmap
      , describe "test union of overlapping maps"    unionWithOverlapping
      , describe "x `union` empty == x"              identity
      , describe "union is idempotent"               idempotent
      , describe "union is associative"              associative
      , describe "union is commutative"              commutative
      ]

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

  definition : Property
  definition = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `difference` fromList kvs2) === fromList ((kvs1 \\\ kvs2) @{keyWise})

  differenceWithSubmap : Property
  differenceWithSubmap = property $ do
    [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
    let submap1   = fromList kvs1
        submap2   = fromList kvs2
        supermap = fromList (kvs1 ++ kvs2)
    (supermap `difference` submap1) === submap2

  nilpotent : Property
  nilpotent = property $ do
    dmap <- forAll genDMap
    (dmap `difference` dmap) === empty

  identity : Property
  identity = property $ do
    dmap <- forAll genDMap
    (dmap `difference` the (DMap K V) empty) === dmap

  domination : Property
  domination = property $ do
    dmap <- forAll genDMap
    (the (DMap K V) empty `difference` dmap) === empty

  export
  differenceProps : Group
  differenceProps
    = MkGroup "`difference` properties"
    $ [ describe "test against the definition"                definition
      , describe "test difference with submap"                differenceWithSubmap
      , describe "x `difference` x == empty"                  nilpotent
      , describe "x `difference` empty == x"                  identity
      , describe "empty `difference` x == empty (domination)" domination
      ]

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

  definition : Property
  definition = property $ do
    [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
    (fromList kvs1 `intersection` fromList kvs2) === fromList (intersect kvs1 kvs2 @{keyWise})

  precedence : Property
  precedence = property $ do
    n <- forAll genParam
    [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

    assertElem (k :=> v1) (insert k v1 dmap1 `intersection` insert k v2 dmap2)

  intersectionWithSubmap : Property
  intersectionWithSubmap = property $ do
    [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
    let submap   = fromList kvs2
        supermap = fromList (kvs1 ++ kvs2)
    (submap `intersection` supermap) === submap

  domination : Property
  domination = property $ do
    a <- forAll genDMap
    (a `intersection` empty) === empty

  idempotent : Property
  idempotent = property $ do
    dmap <- forAll genDMap
    (dmap `intersection` dmap) === dmap

  associative : Property
  associative = property $ do
    [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
    ((a `intersection` b) `intersection` c) === (a `intersection` (b `intersection` c))

  commutative : Property
  commutative = property $ do
    [dmap1, dmap2] <- forAll $ genDMapsConsistent
    (dmap1 `intersection` dmap2) === (dmap2 `intersection` dmap1)

  export
  intersectionProps : Group
  intersectionProps
    = MkGroup "`intersection` properties"
    $ [ describe "test against the definition"                   definition
      , describe "test precedence"                               precedence
      , describe "intersection with submap is the submap"        intersectionWithSubmap
      , describe "intersection with empty is empty (domination)" domination
      , describe "intersection is idempotent"                    idempotent
      , describe "intersection is associative"                   associative
      , describe "intersection is commutative"                   commutative
      ]

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

-- union a b = (a `difference` b) `union` (a `intersection` b) `union` (b `difference` a)
-- a === (a `difference` b) `union` (a `intersection` b)
-- a `difference` (a `difference`   b) === (a `intersection` b)
-- a `difference` (a `intersection` b) === (a `difference`   b)
-- a `difference` (a `intersection` b) `difference` (a `difference` b) === empty

namespace UnionDifferenceIntersection

  -- I came up with these
  prop1, prop2, prop3, prop4, prop5, prop6, prop7 : Property
  prop1 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    (a `difference` (a `difference`   b)) === (a `intersection` b)

  prop2 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    (a `difference` (a `intersection` b)) === (a `difference`   b)

  prop3 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    ((a `difference` (a `intersection` b)) `difference` (a `difference` b)) === empty

  prop4 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    ((a `difference` b) `union` (a `intersection` b)) === a

  prop5 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    (a `union` (b `difference` a)) === (a `union` b)

  prop6 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    let lhs = union a b
        rhs = ((a `difference` b) `union` (a `intersection` b)) `union` (b `difference` a)
    lhs === rhs

  prop7 = property $ do
    [a, b] <- forAll $ np [genDMap, genDMap]
    let lhs = (a `union` b) `difference` (a `intersection` b)
        rhs = (a `difference` b) `union` (b `difference` a)
    lhs === rhs

  export
  lawsICameUpWith : Group
  lawsICameUpWith
    = MkGroup "Laws I came up with"
    $ [ describe "property 1" prop1
      , describe "property 2" prop2
      , describe "property 3" prop3
      , describe "property 4" prop4
      , describe "property 5" prop5
      , describe "property 6" prop6
      , describe "property 7" prop7
      ]

  -- laws from wikipedia
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

  export
  wikipediaLaws : Group
  wikipediaLaws
    = MkGroup "Laws I found on wikipedia"
    $ [ describe "distributive 1" distributive1
      , describe "distributive 2" distributive2
      , describe "absorption 1"   absorption1
      , describe "absorption 2"   absorption2
      ]

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

export
main : IO ()
main = checkGroup toListFromListProps
    *> checkGroup fromListProps
    *> checkGroup eqProps
    *> checkGroup lookupProps
    *> checkGroup insertProps
    *> checkGroup deleteProps
    *> checkGroup emptyProps
    *> checkGroup singletonProps
    *> checkGroup sizeProps
    *> checkGroup unionProps
    *> checkGroup differenceProps
    *> checkGroup intersectionProps
    *> checkGroup lawsICameUpWith
    *> checkGroup wikipediaLaws
    $> ()
