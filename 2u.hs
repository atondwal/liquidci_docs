module Test2 () where
import Prelude hiding (abs)

abs :: Int -> Int
abs x = let b = 0 <= x in
            if b then x else (0 - x)

test2 :: Int -> Int
test2 n = let a = abs n
              b = a + 1
          in
              div n b
