module Test.Data.DMap

import Data.List
import Data.Vect
import Derive.Prelude

import Data.DMap
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

0 Test : Type
Test = (PropertyName, Property)

describe : PropertyName -> PropertyT () -> Test
describe n p = (n, property p)

-- key and value definitions + interface implementations ----------------------
data K : Nat -> Type where
  MkK : String -> (n : Nat) -> K n

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

implementation [keyWise] Eq (DSum K V) where
  (k :=> _) == (k' :=> _) = deq' {f = K} k k'

implementation [paramWise] Eq (DSum K V) where
  (MkK _ n :=> _) == (MkK _ n' :=> _) = n == n'

-- List utils -----------------------------------------------------------------
||| remove all occurances of an element
deleteAll : Eq a => a -> List a -> List a
deleteAll _ []      = []
deleteAll x (y::ys) = (if x == y then [] else [y]) ++ deleteAll x ys

export infix 7 \\\
||| delete all occurances of each element from the right list, in the left list
(\\\) : Eq a => List a -> List a -> List a
(\\\) = foldl (flip deleteAll)

-- TODO this is inefficient
||| Shuffle elements of a list
||| Do it by slicing it in a middle and swapping the sublists multiple times
||| @ ns the indices (moduleo length of the list) at which the list will be sliced
||| @ xs the shuffeled list
shuffle : (ns : List Nat) -> (xs : List a) -> List a
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

||| Slice a list once
||| n the index at which the list will be sliced
||| l the list to be sliced
slice1 : (n : Nat) -> (l : List a) -> (List a, List a)
slice1 n l = let n' = n `mod` length l in (take n' l, drop n' l)

||| Slice a list into multiple sublists
||| @ ns the indices (moduleo length of the list) at which the list will be sliced
slice : Vect n Nat -> List a -> Vect (S n) (List a)
slice ns Nil = [] :: map (const []) ns
slice ns l = go 0 (massage ns) l where

  ||| Massage the numbers, so that they make sense
  massage : Vect k Nat -> Vect k Nat
  massage = sortVect . map (`mod` length l)

  go : Nat -> Vect m Nat -> List a -> Vect (S m) (List a)
  go prevN Nil l = [l]
  go prevN (n :: ns) l = let
    (pre, post) = slice1 (n `minus` prevN) l
    -- we can slice the right sublist, because `n :: ns` is sorted
    in pre :: go n ns post

-- Property utils -------------------------------------------------------------
||| Compare elements of maps
||| Used to compare maps without using the `Eq` implementation
sameElems : DMap K V -> DMap K V -> PropertyT ()
sameElems dmap dmap' = toList dmap === toList dmap'

-- Generators -----------------------------------------------------------------
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

||| Generate list of key-value pairs
genKVs : Gen (List (DSum K V))
genKVs = list defaultRange genKV

||| Generate unique key-value pairs according to a given `Eq` implementation
genKVsUnique : Eq (DSum K V) => Gen (List (DSum K V))
genKVsUnique = nub <$> genKVs

||| Generate a list of key-value pairs, where each key is unique
genKVsUniqueKeys : Gen (List (DSum K V))
genKVsUniqueKeys = genKVsUnique @{keyWise}

||| Generate a list of unique key-value pairs
genKVsUniquePairs : Gen (List (DSum K V))
genKVsUniquePairs = genKVsUnique

||| Generate a non-empty list of key-value pairs
genKVsNonEmpty : Gen (List (DSum K V))
genKVsNonEmpty = toList <$> list1 defaultRange genKV

||| Generate a non-empty list of key-value pairs that are unique according to a
||| given `Eq` implementation
genKVsUniqueNonEmpty : (impl : Eq (DSum K V)) => Gen (List1 (DSum K V))
genKVsUniqueNonEmpty = do
  kv ::: kvs <- list1 defaultRange genKV
  let kvs' = (nub kvs @{impl} \\ [kv]) @{impl}
  pure (kv ::: kvs')

||| Generate a non-empty list of key-value pairs, where each key is unique
genKVsUniqueKeysNonEmpty : Gen (List1 (DSum K V))
genKVsUniqueKeysNonEmpty = genKVsUniqueNonEmpty @{keyWise}

||| Generate a non-empty list of unique key-value pairs
genKVsUniquePairsNonEmpty : Gen (List1 (DSum K V))
genKVsUniquePairsNonEmpty = genKVsUniqueNonEmpty

||| Generate a list of key-value pairs and slice it into a given number of sublists
||| @ n the number of sublists
genKVsDisjoint : (n : Nat) -> Gen (List (DSum K V)) -> Gen (Vect n (List (DSum K V)))
genKVsDisjoint Z gen = pure []
genKVsDisjoint (S n) gen = do
  [kvs, ns] <- np [gen, vect n genNat]
  pure (slice ns kvs)

||| Generate a given number of lists of key-value pairs, disjoint key-wise
genKVsConsistentDisjoint : (n : Nat) -> Gen (Vect n (List (DSum K V)))
genKVsConsistentDisjoint n = genKVsDisjoint n genKVsUniqueKeys

||| Generate two lists of key-value pairs that are potentially overlapping, but
||| consistent, that is, when a key is in both lists, the value paired with it
||| is the same
genKVsConsistentOverlapping : Gen (Vect 2 (List (DSum K V)))
genKVsConsistentOverlapping = do
  [common, kvs1, kvs2] <- genKVsConsistentDisjoint 3
  pure [common ++ kvs1, common ++ kvs2]

-- TODO this should be in `Data.DMap`
theGenDMap : DOrd k => Hedgehog.Range Nat -> Gen (DSum k v) -> Gen (DMap k v)
theGenDMap range gen = fromList <$> list range gen

||| Generate a dependent map
genDMap : Gen (DMap K V)
genDMap = theGenDMap defaultRange genKV

||| Generate two maps that are overlapping, but consistent,
||| that is, when a key is in both maps, the value paired with it is the same
-- when a key is in both maps, the value is the same
genDMapsConsistent : Gen (Vect 2 (DMap K V))
genDMapsConsistent = map fromList <$> genKVsConsistentOverlapping

-- disjoint in the key comparison sense
||| Generate a given number of disjoint maps
genDMapsConsistentDisjoint : (n : Nat) -> Gen (Vect n (DMap K V))
genDMapsConsistentDisjoint n = map fromList <$> genKVsConsistentDisjoint n

-- Tests ----------------------------------------------------------------------
namespace ToListFromList

  -- This should pretty much ensure that both `toList` and `fromList` work correctly.
  -- At least that they preserve all information that a map shaould have.
  preservesInfo : Test
  preservesInfo
    = describe "`toList` and `fromList` preserve the information contained in a map"
    $ do
      kvs <- forAll genKVs
      -- reverse `kvs` so that the last key stays in the `nubbed` list
      DMap.toList (fromList kvs) === sort (nub (reverse kvs) @{keyWise})

  export
  toListFromListProps : Group
  toListFromListProps
    = MkGroup "properties regarding `toList` and `fromList`"
    $ [ preservesInfo
      ]

namespace FromList

  orderInsensitive : Test
  orderInsensitive
    = describe "`fromList` is insensitive to order of lists with unique keys"
    $ do
      [kvs, ns] <- forAll $ np [genKVsUniqueKeys, list defaultRange genNat]
      DMap.fromList kvs `sameElems` fromList (shuffle ns kvs)

  precedence : Test
  precedence
    = describe "test precedence of list elements"
    $ do
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
    $ [ orderInsensitive
      , precedence
      ]

namespace Eq
  reflexive : Test
  reflexive
    = describe "(==) is reflexive"
    $ do
      dmap <- forAll genDMap
      dmap === dmap

  commutative : Test
  commutative
    = describe "(==) is commutative"
    $ do
      [dmap, dmap'] <- forAll $ np [genDMap, genDMap]
      (dmap == dmap') === (dmap' == dmap)

  differentElems : Test
  differentElems
    = describe "maps with different elemetns are not equal"
    $ do
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
    $ [ reflexive
      , commutative
      , differentElems
      ]

namespace Lookup

  lookupExistent : Test
  lookupExistent
    = describe "lookup of an existent key is successful"
    $ do
      [kv@(k :=> _), kvs, kvs'] <- forAll $ np [genKV, genKVs, genKVs]
      let dmap = DMap.fromList (kvs ++ [kv] ++ kvs)

      assert (isJust $ lookup k dmap)

  export
  lookupNonExistent : Test
  lookupNonExistent
    = describe "lookup of a non-existent key is unsuccessful"
    $ do
      (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
      lookup k (fromList kvs) === Nothing

  export
  lookupProps : Group
  lookupProps
    = MkGroup "`lookup` properties"
    $ [ lookupExistent
      , lookupNonExistent
      ]

namespace Insert

  insert1 : Test
  insert1
    = describe "lookup of an inserted element is successful"
    $ do
      [kv@(k :=> v), kvs] <- forAll $ np [genKV, genKVs]

      classify "contains `k`"
        $ any ((==) kv @{keyWise})   kvs
      classify "contains pairs with the same parameter"
        $ any ((==) kv @{paramWise}) kvs
      classify "empty"
        $ kvs == []

      lookup k (insert k v $ fromList kvs) === Just v

  insert2 : Test
  insert2
    = describe "after inserting 2 pairs, lookup of the second is successful"
    $ do
      [kv1@(k1 :=> v1), kv2@(k2 :=> v2), dmap] <- forAll $ np [genKV, genKV, genDMap]

      classify "keys are the same" (deq' k1 k2 {f = K})

      lookup k2 (insert k2 v2 . insert k1 v1 $ dmap) === Just v2

  insertTheSamPairTwice : Test
  insertTheSamPairTwice
    = describe "inserting a pair the second time is uneffectful"
    $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      let dmap'  = insert k v dmap
      let dmap'' = insert k v dmap'

      dmap' === dmap''

  export
  insertProps : Group
  insertProps
    = MkGroup "`insert` properties"
    $ [ insert1
      , insert2
      , insertTheSamPairTwice
      ]

namespace Delete

  delete1 : Test
  delete1
    = describe "lookup of a deleted element is ubsuccesful"
    $ do
      [MkSome k, dmap] <- forAll $ np [genSomeK, genDMap]
      lookup k (delete k dmap) === Nothing

  deleteNonExistent : Test
  deleteNonExistent
    = describe "deletion of a non-existent element is uneffectful"
    $ do
      (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
      let dmap = DMap.fromList kvs

      dmap === delete k dmap

  deleteExistent : Test
  deleteExistent
    = describe "test deletion of an existing key"
    $ do
      (k :=> v) ::: kvs <- forAll genKVsUniqueKeysNonEmpty
      let dmap = DMap.fromList kvs

      dmap === delete k (insert k v dmap)

  export
  deleteProps : Group
  deleteProps
    = MkGroup "`delete` properties"
    $ [ delete1
      , deleteNonExistent
      , deleteExistent
      ]

namespace Empty
  emptyToList : Test
  emptyToList
    = describe "`empty` converted to a list is the empty list"
    $ DMap.toList (the (DMap K V) empty) === []

  fromEmpty : Test
  fromEmpty
    = describe "`empty` is a map constructed from the empty list"
    $ the (DMap K V) empty === fromList []

  lookupInEmpty : Test
  lookupInEmpty
    = describe "lookup in `empty` is unsuccessful"
      $ do
      MkSome k <- forAll genSomeK
      let dmap = the (DMap K V) empty
      lookup k dmap === Nothing

  deleteFromEmpty : Test
  deleteFromEmpty
    = describe "deletion from `empty` is uneffectful"
      $ do
      MkSome k <- forAll genSomeK
      let dmap = the (DMap K V) empty
      dmap === (delete k dmap)

  export
  emptyProps : Group
  emptyProps
    = MkGroup "`empty` properties"
    $ [ emptyToList
      , fromEmpty
      , lookupInEmpty
      , deleteFromEmpty
      ]

namespace Singleton
  singletonToList : Test
  singletonToList
    = describe "a singleton converted to a list is a singleton list"
    $ do
      k :=> v <- forAll genKV
      DMap.toList (the (DMap K V) (singleton k v)) === [k :=> v]

  fromSingleton : Test
  fromSingleton
    = describe "a singleton is a map constructed from a singleton list"
    $ do
      kv@(k :=> v) <- forAll genKV
      singleton k v === fromList [kv]

  lookupInSingleton : Test
  lookupInSingleton
    = describe "lookup in a singleton is successful"
    $ do
      k :=> v <- forAll genKV
      let dmap = the (DMap K V) (singleton k v)
      lookup k dmap === Just v

  insertToEmpty : Test
  insertToEmpty
    = describe "inserting to `empty` returns a singleton"
    $ do
      k :=> v <- forAll genKV
      let lhs, rhs : DMap K V
          lhs = singleton k v
          rhs = insert k v empty
      lhs === rhs

  export
  singletonProps : Group
  singletonProps
    = MkGroup "`singleton` properties"
    $ [ singletonToList
      , fromSingleton
      , lookupInSingleton
      , insertToEmpty
      ]

namespace Size

  definition : Test
  definition
    = describe "test against the definition"
    $ do
      xs <- forAll genKVs
      DMap.size (DMap.fromList xs) === cast {from = Nat, to = Int} (length (nub xs @{keyWise}))

  propDelete : Test
  propDelete
    = describe "size change after deletion"
    $ do
      [MkSome k, dmap] <- forAll $ np [genSomeK, genDMap]

      classify "key present"     (isJust    $ lookup k dmap)
      classify "key not present" (isNothing $ lookup k dmap)

      case lookup k dmap of
        Nothing => size dmap === size (delete k dmap)
        Just _  => size dmap === size (delete k dmap) + 1

  propInsert : Test
  propInsert
    = describe "size change after insertion"
    $ do
      [k :=> v, dmap] <- forAll $ np [genKV, genDMap]

      classify "key present"     (isJust    $ lookup k dmap)
      classify "key not present" (isNothing $ lookup k dmap)

      case lookup k dmap of
        Nothing => size (insert k v dmap) === size dmap + 1
        Just _  => size (insert k v dmap) === size dmap

  -- TODO redundant (`propInsertMultiple`), but simpler
  propInsertTwice : Test
  propInsertTwice
    = describe "size change after two insertions under the same key"
    $ do
      n <- forAll genParam
      [k, v1, v2, dmap] <- forAll $ np [genK n, genV n, genV n, genDMap]

      let dmap'  = insert k v1 dmap
          dmap'' = insert k v2 dmap'

      size dmap' === size dmap''

  propInsertMultiple : Test
  propInsertMultiple
    = describe "size change after multiple insertions under the same key"
    $ do
      [n, m, dmap] <- forAll $ np [genParam, genNat, genDMap]
      [k, v :: vs] <- forAll $ np [genK n, vect (S $ S m) (genV n)]

      let dmap'  = insert k v dmap
          dmap'' = foldr (insert k) dmap' vs

      size dmap' === size dmap''

  export
  sizeProps : Group
  sizeProps
    = MkGroup "`size` properties"
    $ [ definition
      , propDelete
      , propInsert
      , propInsertTwice
      , propInsertMultiple
      ]

namespace Union

  definition : Test
  definition
    = describe "test against the definition"
    $ do
      [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
      (fromList kvs2 `union` fromList kvs1) === fromList (kvs1 ++ kvs2)

  precedence : Test
  precedence
    = describe "union is left-biased"
    $ do
      n <- forAll genParam
      [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

      lookup k (insert k v1 dmap1 `union` insert k v2 dmap2) === Just v1

  unionWithSubmap : Test
  unionWithSubmap
    = describe "union with submap uneffectful"
    $ do
      [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
      let submap   = fromList kvs2
      let supermap = fromList (kvs1 ++ kvs2)
      (supermap `union` submap) === supermap

  unionWithOverlapping : Test
  unionWithOverlapping
    = describe "test union of overlapping maps"
    $ do
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

  identity : Test
  identity
    = describe "x `union` empty == x"
    $ do
      a <- forAll genDMap
      (a `union` empty) === a

  idempotent : Test
  idempotent
    = describe "union is idempotent"
    $ do
      dmap <- forAll genDMap
      (dmap `union` dmap) === dmap

  associative : Test
  associative
    = describe "union is associative"
    $ do
      [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
      ((a `union` b) `union` c) === (a `union` (b `union` c))

  commutative : Test
  commutative
    = describe "union is commutative"
    $ do
      [dmap1, dmap2] <- forAll genDMapsConsistent
      (dmap1 `union` dmap2) === (dmap2 `union` dmap1)

  export
  unionProps : Group
  unionProps
    = MkGroup "`union` properties"
    $ [ definition
      , precedence
      , unionWithSubmap
      , unionWithOverlapping
      , identity
      , idempotent
      , associative
      , commutative
      ]

namespace Difference

  definition : Test
  definition
    = describe "test against the definition"
    $ do
      [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
      (fromList kvs1 `difference` fromList kvs2) === fromList ((kvs1 \\\ kvs2) @{keyWise})

  differenceWithSubmap : Test
  differenceWithSubmap
    = describe "test difference with submap"
    $ do
      [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
      let submap1   = fromList kvs1
          submap2   = fromList kvs2
          supermap = fromList (kvs1 ++ kvs2)
      (supermap `difference` submap1) === submap2

  nilpotent : Test
  nilpotent
    = describe "x `difference` x == empty"
    $ do
      dmap <- forAll genDMap
      (dmap `difference` dmap) === empty

  identity : Test
  identity
    = describe "x `difference` empty == x"
    $ do
      dmap <- forAll genDMap
      (dmap `difference` the (DMap K V) empty) === dmap

  domination : Test
  domination
    = describe "empty `difference` x == empty (domination)"
    $ do
      dmap <- forAll genDMap
      (the (DMap K V) empty `difference` dmap) === empty

  export
  differenceProps : Group
  differenceProps
    = MkGroup "`difference` properties"
    $ [ definition
      , differenceWithSubmap
      , nilpotent
      , identity
      , domination
      ]

namespace Intersection

  definition : Test
  definition
    = describe "test against the definition"
    $ do
      [kvs1, kvs2] <- forAll $ np [genKVs, genKVs]
      (fromList kvs1 `intersection` fromList kvs2) === fromList (intersect kvs1 kvs2 @{keyWise})

  precedence : Test
  precedence
    = describe "intersection is left-biased"
    $ do
      n <- forAll genParam
      [k, v1, v2, dmap1, dmap2] <- forAll $ np [genK n, genV n, genV n, genDMap, genDMap]

      lookup k (insert k v1 dmap1 `intersection` insert k v2 dmap2) === Just v1

  intersectionWithSubmap : Test
  intersectionWithSubmap
    = describe "intersection with submap is the submap"
    $ do
      [kvs1, kvs2] <- forAll (genKVsConsistentDisjoint 2)
      let submap   = fromList kvs2
          supermap = fromList (kvs1 ++ kvs2)
      (submap `intersection` supermap) === submap

  domination : Test
  domination
    = describe "intersection with `empty` is `empty` (domination)"
    $ do
      a <- forAll genDMap
      (a `intersection` empty) === empty

  idempotent : Test
  idempotent
    = describe "intersection is idempotent"
    $ do
      dmap <- forAll genDMap
      (dmap `intersection` dmap) === dmap

  associative : Test
  associative
    = describe "intersection is associative"
    $ do
      [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
      ((a `intersection` b) `intersection` c) === (a `intersection` (b `intersection` c))

  commutative : Test
  commutative
    = describe "intersection is commutative"
    $ do
      [dmap1, dmap2] <- forAll $ genDMapsConsistent
      (dmap1 `intersection` dmap2) === (dmap2 `intersection` dmap1)

  export
  intersectionProps : Group
  intersectionProps
    = MkGroup "`intersection` properties"
    $ [ definition
      , precedence
      , intersectionWithSubmap
      , domination
      , idempotent
      , associative
      , commutative
      ]

namespace UnionDifferenceIntersection

  -- I came up with these
  prop1, prop2, prop3, prop4, prop5, prop6, prop7 : Test
  prop1
    = describe "property 1"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      (a `difference` (a `difference`   b)) === (a `intersection` b)

  prop2
    = describe "property 2"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      (a `difference` (a `intersection` b)) === (a `difference`   b)

  prop3
    = describe "property 3"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      ((a `difference` (a `intersection` b)) `difference` (a `difference` b)) === empty

  prop4
    = describe "property 4"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      ((a `difference` b) `union` (a `intersection` b)) === a

  prop5
    = describe "property 5"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      (a `union` (b `difference` a)) === (a `union` b)

  prop6
    = describe "property 6"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      let lhs = union a b
          rhs = ((a `difference` b) `union` (a `intersection` b)) `union` (b `difference` a)
      lhs === rhs

  prop7
    = describe "property 7"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      let lhs = (a `union` b) `difference` (a `intersection` b)
          rhs = (a `difference` b) `union` (b `difference` a)
      lhs === rhs

  export
  lawsICameUpWith : Group
  lawsICameUpWith
    = MkGroup "Laws I came up with"
    $ [ prop1
      , prop2
      , prop3
      , prop4
      , prop5
      , prop6
      , prop7
      ]

  -- laws from wikipedia
  distributive1, distributive2 : Test
  distributive1
    = describe "distributive 1"
    $ do
      [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
      (a `union` (b `intersection` c)) === ((a `union` b) `intersection` (a `union` c))

  distributive2
    = describe "distributive 2"
    $ do
      [a, b, c] <- forAll $ np [genDMap, genDMap, genDMap]
      (a `intersection` (b `union` c)) === ((a `intersection` b) `union` (a `intersection` c))

  absorption1, absorption2 : Test
  absorption1
    = describe "absorption 1"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      (a `union` (a `intersection` b)) === a

  absorption2
    = describe "absorption 2"
    $ do
      [a, b] <- forAll $ np [genDMap, genDMap]
      (a `intersection` (a `union` b)) === a

  export
  wikipediaLaws : Group
  wikipediaLaws
    = MkGroup "Laws I found on wikipedia"
    $ [ distributive1
      , distributive2
      , absorption1
      , absorption2
      ]

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
