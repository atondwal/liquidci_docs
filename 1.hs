module Test1 () where
-- Step 1: Write down the set of CONSTRAINTS with KVars

-- Γ represents the imported environment (Prelude)

inc :: Int -> Int
-- wf: Γ ⊦ x:κx
-- wf: Γ;x:κx ⊦ κ1
inc x = x + 1
--   Γ;x:κx ⊦ κx <: Int
--   Γ;x:κx ⊦ {v:Int | v = 1}  <: Int
-- Γ;x:κx ⊦ {v = x+1} <: κ1


test1 :: Int -> Int
-- Γ ⊦ n:κn
-- Γ n:κn ⊦ κ2
test1 n = let b = 0 <= n in
          -- wf: Γ;n:κn ⊦ κiflet
          -- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif <: κiflet
          if b then
          -- wf: Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif
            let a = inc n
            -- wf: Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet
            -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κn <: κx
            in
               div n a
               -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κn <: Int
               -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κ1[x := n] <: {v:Int|¬(v=0)}
            -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ Int <:κlet
          -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet <: κif
          else
            1
            -- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = False} ⊦ {v:Int | v=1} <: κif

{-

Constriants:

-- Γ ⊦ x:κx
-- Γ;x:κx ⊦ κ1
-- Γ;n:κn ⊦ κiflet
-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet
-- Γ ⊦ n:κn
-- Γ n:κn ⊦ κ2

-- Γ;x:κx ⊦ {v = x+1} <: κ1
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κn <: κx
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ Int <:κlet
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet <: κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = False} ⊦ {v:Int | v=1} <: κif
-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif <: κiflet

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κn <: Int
-- Γ;x:κx ⊦ κx <: Int
-- Γ;x:κx ⊦ {v:Int | v = 1}  <: Int
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κ1[x := n] <: {v:Int|¬(v=0)}

Step 2: Figure out the SOLUTION of the KVars using the given qualifiers

QInst(⋯) = { 0 <= v, 0 <= a, 0 <= n, 0 <= b, 0 <= x }

-- last predicate removed by refine when checking that our
-- refined type is well-formed, by checking that the refinements are
-- well-sorted

Inital Solution:

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ1      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ ⊦ x:κx

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ;x:κx ⊦  κ1

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ;n:κn ⊦ κiflet

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet

κn      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ ⊦ n:κn

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= a /\ 0 <= n /\ 0 <= x /\ 0 <= b }

-- Γ n:κn ⊦ κ2

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Done with the well-formedness constraints!

-- Γ;x:κx ⊦ {v = x+1} <: κ1

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κn <: κx

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= v /\ 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ Int <: κlet

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= n }
κif     =  {v:Int | 0 <= v /\ 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True} ⊦ κlet <: κif

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= n }
κif     =  {v:Int | 0 <= n }
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = False} ⊦ {v:Int | v=1} <: κif

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= n }
κif     =  {v:Int}
κiflet  =  {v:Int | 0 <= v /\ 0 <= n } 
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

-- Γ;n:κn;b:{Prop v <=> 0 <= n} ⊦ κif <: κiflet

κn      =  {v:Int | 0 <= v }
κx      =  {v:Int | 0 <= v }
κ1      =  {v:Int | 0 <= v /\ 0 <= x }
κlet    =  {v:Int | 0 <= n }
κif     =  {v:Int}
κiflet  =  {v:Int}
κ2      =  {v:Int | 0 <= v /\ 0 <= n }

We don't have to make any more passes with these constraints, because
all the constraints with a kvar on the rhs is satisfied.

-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κn <: Int ✓
-- Γ;x:κx ⊦ κx <: Int ✓
-- Γ;x:κx ⊦ {v:Int | v = 1}  <: Int ✓
-- Γ;n:κn;b:{Prop v <=> 0 <= n};b:{v = True};a:κ1[x := n] ⊦ κ1[x := n] <: {v:Int|¬(v=0)} FAILURE

So we fail with the error:
Inferred type {v:Int | 0 <= v /\ 0 <= n }
is not a subtype of required type {v:Int|¬(v=0)}

-}
