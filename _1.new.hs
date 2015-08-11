module Test1 (test1) where
-- export: 0 ⊦ κn <: {v:Int}
-- @TODO is that how this works? we enforce the domain of exported functions as unrefined, unless otherwise specified?
import Prelude hiding (leq,div)

{-@ plus :: x:Int -> y:Int -> {v:Int | v == x + y} @-}
plus :: Int -> Int -> Int
plus x y = undefined

{-@ leq :: x:Int -> y:Int -> {v:Int| (v == 1) => (x <= y)} @-}
leq :: Int -> Int -> Int
leq x y = undefined

{-@ div:: x:Int -> y:{v:Int|v /= 0} -> Int @-}
div :: Int -> Int -> Int
div = undefined

inc :: Int -> Int
-- wf: 0 ⊦ x:κx → κ1
--  becomes
-- wf: 0 ⊦ x:κx
-- wf: x:κx ⊦  κ1
inc x = plus x 1
-- x:κx ⊦ κx <: Int
-- x:κx ⊦ {v == 1}  <: Int
-- x:κx ⊦ {v == x+y}[x:= x][y:=1] <: κ1

test1 :: Int -> Int
-- wf: 0 ⊦ n:κn → κ2
--  becomes
-- wf: 0 ⊦ n:κn
-- wf: n:κn ⊦ κ2
test1 n = let t = leq 0 n in
          -- wf: n:κn ⊦ κlet1
          -- n:κn ⊦ {v=0} <: {v:Int}
          -- n:κn ⊦ κn <: {v:Int}
          case t of
          -- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ κcase
            1 -> let a = inc n in
                   -- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κlet
                     -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κn <: κx
                     div n a
                     -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ κn <: {v:Int}
                     -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ κ1[x:=n] <: {v /= 0}
                 -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ {v:Int} <: κlet
            -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κlet <: κcase
            _ -> 10
            -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ {v == 10} <: κcase
          -- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ κcase <: κlet1
-- n:κn ⊦ κlet1 <: κ2

-- Step 2: Figure out the SOLUTION of the KVars using the given qualifiers

{-

Gathering all the constraints that have kvars:

(Ommiting base type in a lot of places, since here it's always Int)

-- x:κx ⊦ κx <: Int
-- x:κx ⊦ {v == 1}  <: Int
-- x:κx ⊦ {v == x+y}[x:= x][y:=1] <: κ1

-- n:κn ⊦ {v=0} <: {v:Int}
-- n:κn ⊦ κn <: {v:Int}

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κn <: κx
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ κn <: {v:Int}
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ κ1[x:=n] <: {v /= 0}
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ {v:Int} <: κlet
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κlet <: κcase
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ {v == 10} <: κcase
-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ κcase <: κlet1
-- n:κn ⊦ κlet1 <: κ2

-- wf: 0 ⊦ x:κx
-- wf: x:κx ⊦  κ1

-- wf: 0 ⊦ n:κn
-- wf: n:κn ⊦ κ2

-- wf: n:κn ⊦ κlet1

-- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n]  ⊦ κcase
-- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κlet

-- export: 0 ⊦ κn <: {v:Int}

We start by assiging all the kvars QInst(Γ,e,ℚ)

QInst(⋯) = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

So our inital solution to be refined is

κx     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κn     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ1     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet1  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

We consider the constraint

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ κ1[x:=n] <: {v /= 0}

and realize that it cannot be satisfied by removing any number of qualifiers from kvars, since the rhs is of the form {v : T | phi}.

We proceed to calculate the kvars anyways:

The first constraint that needs to be weakened is

-- wf: 0 ⊦ x:κx
-- wf: 0 ⊦ x:{ 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

which gets weakened to

-- wf: 0 ⊦ x:{ 0 <= v, 0 <= x }

so that we have

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ1     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet1  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

Then,

-- wf: 0 ⊦ n:κn
-- wf: 0 ⊦ n:{ 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

weakens

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet1  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

-- wf: x:κx ⊦  κ1

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }

-- wf: n:κn ⊦ κ2

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- wf: n:κn ⊦ κlet1


κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n]  ⊦ κcase

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= a, 0 <= n, 0 <= x, 0 <= y, 0 <= t }
κcase  = { 0 <= v, 0 <= n, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- wf: n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κlet

κx     = { 0 <= v, 0 <= x }
κn     = { 0 <= v, 0 <= n }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { 0 <= v, 0 <= n, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- export: 0 ⊦ κn <: {v:Int}

κx     = { 0 <= v, 0 <= x }
κn     = { true }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { 0 <= v, 0 <= n, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1} ⊦ κn <: κx
-- @TODO What do we do when we have user annotations that don't take the form of qualifers but are still in EUFA?

κx     = { true }
κn     = { true }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { 0 <= v, 0 <= n, 0 <= t }
κ2     = { 0 <= v, 0 <= n }

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ {v == 10} <: κcase

κx     = { true }
κn     = { true }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { 0 <= v, 0 <= n }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { true }
κ2     = { 0 <= v, 0 <= n }

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n] ⊦ κcase <: κlet1

κx     = { true }
κn     = { true }
κ1     = { 0 <= v, 0 <= x }
κlet1  = { true }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { true }
κ2     = { 0 <= v, 0 <= n }

-- x:κx ⊦ {v == x+y}[x:= x][y:=1] <: κ1

κx     = { true }
κn     = { true }
κ1     = { true }
κlet1  = { true }
κlet   = { 0 <= v, 0 <= n, 0 <= t }
κcase  = { true }
κ2     = { 0 <= v, 0 <= n }

-- n:κn;t:{v:Int| (v == 1) => (x <= y)}[x:=0][y:=n];t:{v == 1};a:κ1[x:=n] ⊦ {v:Int} <: κlet

κx     = { true }
κn     = { true }
κ1     = { true }
κlet1  = { true }
κlet   = { true }
κcase  = { true }
κ2     = { 0 <= v, 0 <= n }

-- n:κn ⊦ κlet1 <: κ2

κx     = { true }
κn     = { true }
κ1     = { true }
κlet1  = { true }
κlet   = { true }
κcase  = { true }
κ2     = { true }

-}
