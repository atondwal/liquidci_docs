module Test2 () where
import Prelude hiding (abs)

abs :: Int -> Int
abs x = let b = 0 <= x in
            if b then x else (0 + x)

test2 :: Int -> Int -> Int
test2 n m = let a = abs n
                b = abs m
                c' = b + 1
                c = a + c'
            in
              div n c
