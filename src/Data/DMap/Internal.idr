{- Copied from haskell's dependent-map package -}
module Data.DMap.Internal

import Control.Monad.State
import Data.Maybe

import Data.DSum
import Data.GCompare
import Data.GEq
import Data.ShowS
import Data.Some

||| Dependent maps: 'k' is a GADT-like thing with a facility for
||| rediscovering its type parameter, elements of which function as identifiers
||| tagged with the type of the thing they identify.  Real GADTs are one
||| useful instantiation of `k`, as are 'Tag's from "Data.Unique.Tag" in the
||| 'prim-uniq' package.
|||
||| Semantically, `'DMap' k f` is equivalent to a set of `'DSum' k f` where no two
||| elements have the same tag.
|||
||| More informally, 'DMap' is to dependent products as 'M.Map' is to `(->)`.
||| Thus it could also be thought of as a partial (in the sense of \"partial
||| function\") dependent product.
public export
data DMap : (k : a -> Type) -> (f : a -> Type) -> Type where
    Tip : DMap k f
    Bin : (sz    : Int)
       -> (key   : k v)
       -> (value : f v)
       -> (left  : DMap k f)
       -> (right : DMap k f)
       -> DMap k f

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

||| *O(1)*. The empty map.
|||
||| ```
||| empty      == fromList []
||| size empty == 0
||| ```
export
empty : DMap k f
empty = Tip

||| *O(1)*. A map with a single element.
|||
||| ```
||| singleton 1 'a'        == fromList [(1, 'a')]
||| size (singleton 1 'a') == 1
||| ```
export
singleton : {0 v : a} -> k v -> f v -> DMap k f
singleton k x = Bin 1 k x Tip Tip

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

||| *O(1)*. Is the map empty?
export
null : DMap k f -> Bool
null Tip              = True
null (Bin _ _ _ _ _)  = False

||| *O(1)*. The number of elements in the map.
export
size : DMap k f -> Int
size Tip                = 0
size (Bin n _ _ _ _)    = n

||| *O(log n)*. Lookup the value at a key in the map.
|||
||| The function will return the corresponding value as `('Just' value)`,
||| or 'Nothing' if the key isn't in the map.
export
lookup : (impl : GCompare k) => k v -> DMap k f -> Maybe (f v)
lookup k Tip = Nothing
lookup k (Bin _ kx x l r) = case gcompare k kx @{impl} of
  GLT => lookup k l
  GGT => lookup k r
  GEQ => Just x

export
lookupAssoc : (impl : GCompare k) => Some k -> DMap k f -> Maybe (DSum k f)
lookupAssoc sk = withSome sk $ \key =>
  let
    go : DMap k f -> Maybe (DSum k f)
    go Tip = Nothing
    go (Bin _ kx x l r) =
        case gcompare key kx @{impl} of
            GLT => go l
            GGT => go r
            GEQ => Just (kx :=> x)
  in go

{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.

  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [combine k x l r] Restores balance and size.

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [combine], [merge] and [balance].
  Quickcheck (on [difference]) showed that this was necessary in order
  to maintain the invariants. It is quite unsatisfactory that I haven't
  been able to find out why this is actually the case! Fortunately, it
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}
export
delta, ratio : Int
delta = 4
ratio = 2


{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
export
bin : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
bin k x l r
  = Bin (size l + size r + 1) k x l r



-- basic rotations
export
singleL, singleR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _ _ _ Tip = assert_total $ idris_crash "error: singleL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
singleR _ _ Tip _ = assert_total $ idris_crash "error: singleR Tip"

export
doubleL, doubleR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL _ _ _ _ = assert_total $ idris_crash "error: doubleL"
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR _ _ _ _ = assert_total $ idris_crash "error: doubleR"


-- rotate
export
rotateL : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
rotateL k x l r@(Bin _ _ _ ly ry)
  = if size ly < ratio*size ry then singleL k x l r
                               else doubleL k x l r
rotateL _ _ _ Tip = assert_total $ idris_crash "error: rotateL Tip"

export
rotateR : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
rotateR k x l@(Bin _ _ _ ly ry) r
  = if size ry < ratio*size ly then singleR k x l r
                               else doubleR k x l r
rotateR _ _ Tip _ = assert_total $ idris_crash "error: rotateR Tip"


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It corresponds with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do, and in practice, a rather large
    [delta] may perform better than smaller one.

  Note: in contrast to Adam's paper, we use a ratio of (at least) [2]
  to decide whether a single or double rotation is needed. Although
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses an invalid ratio of [1].
--------------------------------------------------------------------}
export
balance : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f -> DMap k f
balance k x l r
  =    if sizeL + sizeR <= 1   then Bin sizeX k x l r
  else if sizeR >= delta*sizeL then rotateL k x l r
  else if sizeL >= delta*sizeR then rotateR k x l r
  else                              Bin sizeX k x l r

  where
    sizeL, sizeR, sizeX : Int
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1


{--------------------------------------------------------------------
  Combine
--------------------------------------------------------------------}

-- insertMin and insertMax don't perform potentially expensive comparisons.
export
insertMax, insertMin : {0 v : a} -> k v -> f v -> DMap k f -> DMap k f
insertMax kx x t
  = case t of
      Tip => singleton kx x
      Bin _ ky y l r
          => balance ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip => singleton kx x
      Bin _ ky y l r
          => balance ky y (insertMin kx x l) r

export
combine : GCompare k => k v -> f v -> DMap k f -> DMap k f -> DMap k f
combine kx x Tip r  = insertMin kx x r
combine kx x l Tip  = insertMax kx x l
combine kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  =    if delta*sizeL <= sizeR then balance kz z (combine kx x l lz) rz
  else if delta*sizeR <= sizeL then balance ky y ly (combine kx x ry r)
  else                              bin kx x l r

||| *O(log n)*. Retrieves the minimal (key :=> value) entry of the map, and
||| the map stripped of that element, or 'Nothing' if passed an empty map.
export
minViewWithKey : DMap k f -> Maybe (DSum k f, DMap k f)
minViewWithKey Tip = Nothing
minViewWithKey (Bin _ k0 x0 l0 r0) = Just $ go k0 x0 l0 r0
  where
    go : {0 k, f : a -> Type} -> k v -> f v -> DMap k f -> DMap k f -> (DSum k f, DMap k f)
    go k x Tip r = (k :=> x, r)
    go k x (Bin _ kl xl ll lr) r =
      let (km, l') = go kl xl ll lr
      in (km, balance k x l' r)

||| *O(log n)*. Retrieves the maximal (key :=> value) entry of the map, and
||| the map stripped of that element, or 'Nothing' if passed an empty map.
export
maxViewWithKey : DMap k f -> Maybe (DSum k f, DMap k f)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k0 x0 l0 r0) = Just $ go k0 x0 l0 r0
  where
    go : k v -> f v -> DMap k f -> DMap k f -> (DSum k f, DMap k f)
    go k x l Tip = (k :=> x, l)
    go k x l (Bin _ kr xr rl rr) =
      let (km, r') = go kr xr rl rr
      in (km, balance k x l r')

||| *O(log n)*. Delete and find the maximal element.
|||
||| ```
||| deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
||| deleteFindMax empty                                      Error: can not return the maximal element of an empty map
||| ```
export
deleteFindMax : DMap k f -> (DSum k f, DMap k f)
deleteFindMax t
  = case t of
      Bin _ k x l Tip => (k :=> x,l)
      Bin _ k x l r   => let (km,r') = deleteFindMax r in (km,balance k x l r')
      --Tip             => (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)
      Tip             => (assert_total $ idris_crash "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)

||| *O(log n)*. Delete and find the minimal element.
|||
||| ```
||| deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")])
||| deleteFindMin                                            Error: can not return the minimal element of an empty map
||| ```
export
deleteFindMin : DMap k f -> (DSum k f, DMap k f)
deleteFindMin t = case minViewWithKey t of
  Nothing => (assert_total $ idris_crash "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)
  Just p => p

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
export
glue : DMap k f -> DMap k f -> DMap k f
glue Tip r = r
glue l Tip = l
glue l r =
  if size l > size r then case deleteFindMax l of (km :=> m, l') => balance km m l' r
                     else case deleteFindMin r of (km :=> m, r') => balance km m l r'

{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
export
merge : DMap k f -> DMap k f -> DMap k f
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  =    if delta*sizeL <= sizeR then balance ky y (merge l ly) ry
  else if delta*sizeR <= sizeL then balance kx x lx (merge rx r)
  else                              glue l r


{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo k]
  should be read as [compare lo k].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo k == LT]
                        and [cmphi k == GT] for the key [k] of the root.
  [filterGt cmp t]      A tree where for all keys [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all keys [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
export
trim : (Some k -> Ordering) -> (Some k -> Ordering) -> DMap k f -> DMap k f
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ kx _ l r)
  = case cmplo (MkSome kx) of
      LT => case cmphi (MkSome kx) of
              GT => t
              _  => trim cmplo cmphi l
      _  => trim cmplo cmphi r

export
trimLookupLo : GCompare k => Some k -> (Some k -> Ordering) -> DMap k f -> (Maybe (DSum k f), DMap k f)
trimLookupLo _  _     Tip = (Nothing,Tip)
trimLookupLo lo cmphi t@(Bin _ kx x l r)
  = case compare lo (MkSome kx) @{viaGCompare} of
      LT => case cmphi (MkSome kx) of
              GT => (lookupAssoc lo t, t)
              _  => trimLookupLo lo cmphi l
      GT => trimLookupLo lo cmphi r
      EQ => (Just (kx :=> x), trim (compare lo @{viaGCompare}) cmphi r)

{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
export
filterGt : GCompare k => (Some k -> Ordering) -> DMap k f -> DMap k f
filterGt cmp = go
  where
    go : DMap k f -> DMap k f
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (MkSome kx) of
              LT => combine kx x (go l) r
              GT => go r
              EQ => r

export
filterLt : GCompare k => (Some k -> Ordering) -> DMap k f -> DMap k f
filterLt cmp = go
  where
    go : DMap k f -> DMap k f
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (MkSome kx) of
          LT => go l
          GT => combine kx x l (go r)
          EQ => l
