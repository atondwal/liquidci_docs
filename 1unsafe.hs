module Test1 () where
inc :: Int -> Int
inc x = x - 1

test1 :: Int -> Int
test1 n = let b = 0 <= n in
          if b then
            let a = inc n
            in
               div n a
          else
            1

{-

Constriants:

-- Γ ⊦ x:κx
-- Γ;x:κx ⊦ κ1
-- Γ;n:κn ⊦ κiflet
-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet
-- Γ ⊦ n:κn
-- Γ n:κn ⊦ κ2

-- Γ;x:κx ⊦ {v = x-1} <: κ1
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κn <: κx
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ Int <:κlet
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet <: κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = False} ⊦ {v:Int | v=1} <: κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif <: κiflet

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κn <: Int
-- Γ;x:κx ⊦ κx <: Int
-- Γ;x:κx ⊦ {v:Int | v = 1}  <: Int
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κ1[x := n] <: {v:Int|¬(v=0)}

-}
