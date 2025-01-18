module Data.DMapGen

import Data.DMap
import Hedgehog

{--------------------------------------------------------------------
  Arbitrary maps
--------------------------------------------------------------------}

||| Generates a map using a 'Range' to determine the size.
export
genDMap : DOrd k => Hedgehog.Range Nat -> Gen (DSum k v) -> Gen (DMap k v)
genDMap range gen = fromList <$> list range gen
