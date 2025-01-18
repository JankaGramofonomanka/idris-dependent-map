module Main

import Test.Data.DMap

main : IO ()
main = do
  True <- Test.Data.DMap.spec
        | False => assert_total (idris_crash "tests failed")
  pure ()
