module Test2 () where
import Prelude hiding (abs)

-- Step 1: Write down the set of CONSTRAINTS with KVars

-- Γ represents the imported environment (Prelude, etc)

abs :: Int -> Int
-- wf: Γ x:κx ⊦ κ1
-- wf: Γ ⊦ x:κx
abs x = let b = 0 <= x in
            if b then x else (0 - x)
-- wf: Γ;x:κx ⊦ κiflet
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet
--   Γ;x:κx;b:{Prop v <=> 0<=x};b ⊦ x <: κif
--     Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0} <: Int
--     Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=x} <: Int
--   Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0-x} <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1

test2 :: Int -> Int
-- wf: Γ ⊦ n:κn
-- wf: Γ n:κn ⊦ κ2
test2 n = let a = abs n
            -- wf: Γ ⊦ κlet
            -- Γ ⊦ κlet <: κ2
            -- Γ ⊦ κn <: κx
              b = a + 1
            -- Γ;a:κ1[x := n] ⊦ κ1 <: Int
            -- Γ;a:κ1[x := n] ⊦ {v:Int|v=1} <: Int
          in
              div n b
               -- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ κn <: Int
               -- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ {v:Int|v=a+1} <: {v:Int|¬(v=0)}
             -- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ Int <: κlet

{-

Constriants:

-- wf: Γ ⊦ x:κx
-- wf: Γ x:κx ⊦ κ1
-- wf: Γ;x:κx ⊦ κiflet
-- wf: Γ ⊦ n:κn
-- wf: Γ n:κn ⊦ κ2
-- wf: Γ ⊦ κlet
-- wf: Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet
-- Γ;x:κx;b:{Prop v <=> 0<=x};b ⊦ x <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0-x} <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1
-- Γ ⊦ κlet <: κ2
-- Γ ⊦ κn <: κx
-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ Int <: κlet

-- Γ;a:κ1[x := n] ⊦ κ1 <: Int
-- Γ;a:κ1[x := n] ⊦ {v:Int|v=1} <: Int
-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ κn <: Int
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0} <: Int
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=x} <: Int
-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ {v:Int|v=a+1} <: {v:Int|¬(v=0)}

Step 2: Figure out the SOLUTION of the KVars using the given qualifiers

QInst(⋯) = { 0 <= v, 0 <= a, 0 <= n, 0 <= b, 0 <= x }

Inital Solution:

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ1      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- wf: Γ ⊦ x:κx

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- wf: Γ x:κx ⊦ κ1

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- wf: Γ;x:κx ⊦ κiflet

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- wf: Γ ⊦ n:κn

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- wf: Γ n:κn ⊦ κ2

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- wf: Γ ⊦ κlet

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- wf: Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v }
κif     =  {v:Int | 0 <= v /\ 0 <= x }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

Done with the wf constraints!

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v }
κif     =  {v:Int | 0 <= v /\ 0 <= x }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0-x} <: κif

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v }
κif     =  {v:Int | 0 <= v }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v }
κif     =  {v:Int | 0 <= v }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ ⊦ κlet <: κ2

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int}
κif     =  {v:Int | 0 <= v }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ ⊦ κn <: κx

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int}
κif     =  {v:Int | 0 <= v }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ Int <: κlet

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int}
κif     =  {v:Int | 0 <= v }
κiflet  =  {v:Int | 0 <= v /\ 0 <= x }
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

We don't have to make any more passes with these constraints, because
all the constraints with a kvar on the rhs is satisfied.

-- Γ;a:κ1[x := n] ⊦ κ1 <: Int ✓
-- Γ;a:κ1[x := n] ⊦ {v:Int|v=1} <: Int ✓
-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ κn <: Int ✓
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=0} <: Int ✓
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v:Int|v=x} <: Int ✓
-- Γ;a:κ1[x := n];b:{v:Int|v=a+1} ⊦ {v:Int|v=a+1} <: {v:Int|¬(v=0)} ✓

-}
