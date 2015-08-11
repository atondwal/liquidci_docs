module Test2 () where
import Prelude hiding (abs)

abs :: Int -> Int
-- wf: Γ x:κx ⊦ κ1
-- wf: Γ ⊦ x:κx
abs x = let b = 0 <= x in
            if b then x else (0 - x)
-- wf: Γ;x:κx ⊦ κiflet
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet
--   Γ;x:κx;b:{Prop v <=> 0<=x};b ⊦ {v=x} <: κif
--     Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0} <: Int
--     Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=x} <: Int
--   Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0-x} <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1

test2 :: Int -> Int -> Int
-- wf: Γ ⊦ n:κn
-- wf: Γ;n:κn ⊦ m:κm
-- wf: Γ;n:κn;m:κm ⊦ κ2
test2 n m = let a = abs n
            -- wf: Γ ⊦ κlet
            -- Γ ⊦ κlet <: κ2
            -- Γ ⊦ κn <: κx
                b = abs m
            -- Γ;a:κ1[x := n] ⊦ κm <: κx
                c' = b + 1
                c = a + c'
            -- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=b} <: Int
            -- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=1} <: Int
            -- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=c'} <: Int
            -- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=a} <: Int
            -- let G = Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1}
            in
              div n c
               -- G;c:{v=a+c'} ⊦ κn <: Int
               -- G;c:{v=a+c'} ⊦ {v=c} <: {v:Int|¬(v=0)}
             -- G;c:{v=a+c'} ⊦ Int <: κlet

{-

Constriants:

-- Γ ⊦ x:κx
-- Γ x:κx ⊦ κ1
-- Γ;x:κx ⊦ κiflet
-- Γ ⊦ n:κn
-- Γ;n:κn ⊦ m:κm
-- Γ;n:κn;m:κm ⊦ κ2
-- Γ ⊦ κlet
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet
-- Γ;x:κx;b:{Prop v <=> 0<=x};b ⊦ {v=x} <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0-x} <: κif
-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1
-- Γ ⊦ κlet <: κ2
-- Γ ⊦ κn <: κx
-- Γ;a:κ1[x := n] ⊦ κm <: κx
-- G;c:{v:Int|v=a+c'} ⊦ Int <: κlet

-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0} <: Int
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=x} <: Int
-- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=b} <: Int
-- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=1} <: Int
-- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=c'} <: Int
-- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=a} <: Int
-- G;c:{v:Int|v=a+c'} ⊦ κn <: Int
-- G;c:{v:Int|v=a+c'} ⊦ {v=c} <: {v:Int|¬(v=0)}

Vars: v,x,n,m,a,b,c,c'

0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

Initally:

κx = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ1 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κiflet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κn = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κm = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ ⊦ x:κx

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κiflet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κn = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κm = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ x:κx ⊦ κ1

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κn = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κm = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ;x:κx ⊦ κiflet

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x
κn = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κm = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ ⊦ n:κn

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x
κn = 0 <= v
κm = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ;n:κn ⊦ m:κm

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x
κn = 0 <= v
κm = 0 <= v /\ 0 <= n
κ2 = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ;n:κn;m:κm ⊦ κ2

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x
κn = 0 <= v
κm = 0 <= v /\ 0 <= n
κ2 = 0 <= v /\ 0 <= n /\ 0 <= m
ĸlet = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ ⊦ κlet

κx = 0 <= v
κ1 = 0 <= v /\ 0 <= x
κiflet = 0 <= v /\ 0 <= x
κn = 0 <= v
κm = 0 <= v /\ 0 <= n
κ2 = 0 <= v /\ 0 <= n /\ 0 <= m
ĸlet = 0 <= v
κif = 0 <= v /\ 0 <= x /\ 0 <= n /\ 0 <= m /\ 0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= c'

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v /\ 0 <= n /\ 0 <= m
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

*** wfs done ***

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κif <: κiflet

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v /\ 0 <= n /\ 0 <= m
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ;x:κx;b:{Prop v <=> 0<=x};b ⊦ {x=v} <: κif

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v /\ 0 <= n /\ 0 <= m
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0-x} <: κif

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v /\ 0 <= n /\ 0 <= m
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ;x:κx;b:{Prop v <=> 0<=x} ⊦ κiflet <: κ1

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v /\ 0 <= n /\ 0 <= m
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ ⊦ κlet <: κ2

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ ⊦ κn <: κx

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- Γ;a:κ1[x := n] ⊦ κm <: κx

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v
ĸlet    =  0 <= v
κif     =  0 <= v /\ 0 <= x

-- G;c:{v:Int|v=a+c'} ⊦ Int <: κlet

κx      =  0 <= v
κ1      =  0 <= v /\ 0 <= x
κiflet  =  0 <= v /\ 0 <= x
κn      =  0 <= v
κm      =  0 <= v /\ 0 <= n
κ2      =  0 <= v
ĸlet    =  true
κif     =  0 <= v /\ 0 <= x

-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=0} <: Int ✓
-- Γ;x:κx;b:{Prop v <=> 0<=x};¬b ⊦ {v=x} <: Int ✓
-- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=b} <: Int ✓
-- Γ;a:κ1[x := n];b:κ1[x := m] ⊦ {v=1} <: Int ✓
-- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=c'} <: Int ✓
-- Γ;a:κ1[x := n];b:κ1[x := m];c':{v=b+1} ⊦ {v=a} <: Int ✓
-- G;c:{v:Int|v=a+c'} ⊦ κn <: Int ✓
-- G;c:{v:Int|v=a+c'} ⊦ {v=c} <: {¬(v=0)} FAILURE

-}