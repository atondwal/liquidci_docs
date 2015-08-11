module Foo (main) where

data Peano = Z | S Peano

foo       :: Peano -> Int
foo Z     = 0
foo (S n) = let r = foo n
             in 1 + r

-- Γ ⊦ K
-- Γ;tmp:{v=Z} ⊦ {v=0} <: K
-- Γ;tmp:{v=S n};n:{v=n} ⊦ {v=n} <: Peano
-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K


main :: Peano -> Int
main p = let q  = foo p
             q' = (1 + q)
          in div 100 q'

-- Γ;p:Peano ⊦ κlet
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=1} <: Int
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=q} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=100} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=q'} <: {v/=0}


{-

QUALIFS: {v = 0, v = 1, v = 2, v = 3, 0 <= v, 0 < v, v < 0, v <= 0}
vars: {tmp,n,p,q,q',r}

Constraints:

-- Γ ⊦ K
-- Γ;p:Peano ⊦ κlet

-- Γ;tmp:{v=Z} ⊦ {v=0} <: K
-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K

-- Γ;tmp:{v=S n};n:{v=n} ⊦ {v=n} <: Peano
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=1} <: Int
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=q} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=100} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=q'} <: {v/=0}

Inital assignment:

K = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0 /\ n = 0 /\ n = 1 /\ n = 2 /\ n = 3 /\ 0 <= n /\ 0 < n /\ n < 0 /\ n <= 0 /\ p = 0 /\ p = 1 /\ p = 2 /\ p = 3 /\ 0 <= p /\ 0 < p /\ p < 0 /\ p <= 0 /\ q = 0 /\ q = 1 /\ q = 2 /\ q = 3 /\ 0 <= q /\ 0 < q /\ q < 0 /\ q <= 0 /\ r = 0 /\ r = 1 /\ r = 2 /\ r = 3 /\ 0 <= r /\ 0 < r /\ r < 0 /\ r <= 0 /\ tmp = 0 /\ tmp = 1 /\ tmp = 2 /\ tmp = 3 /\ 0 <= tmp /\ 0 < tmp /\ tmp < 0 /\ tmp <= 0 /\ q' = 0 /\ q' = 1 /\ q' = 2 /\ q' = 3 /\ 0 <= q' /\ 0 < q' /\ q' < 0 /\ q' <= 0
κlet = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0 /\ n = 0 /\ n = 1 /\ n = 2 /\ n = 3 /\ 0 <= n /\ 0 < n /\ n < 0 /\ n <= 0 /\ p = 0 /\ p = 1 /\ p = 2 /\ p = 3 /\ 0 <= p /\ 0 < p /\ p < 0 /\ p <= 0 /\ q = 0 /\ q = 1 /\ q = 2 /\ q = 3 /\ 0 <= q /\ 0 < q /\ q < 0 /\ q <= 0 /\ r = 0 /\ r = 1 /\ r = 2 /\ r = 3 /\ 0 <= r /\ 0 < r /\ r < 0 /\ r <= 0 /\ tmp = 0 /\ tmp = 1 /\ tmp = 2 /\ tmp = 3 /\ 0 <= tmp /\ 0 < tmp /\ tmp < 0 /\ tmp <= 0 /\ q' = 0 /\ q' = 1 /\ q' = 2 /\ q' = 3 /\ 0 <= q' /\ 0 < q' /\ q' < 0 /\ q' <= 0

-- Γ ⊦ K

K = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0
κlet = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0 /\ n = 0 /\ n = 1 /\ n = 2 /\ n = 3 /\ 0 <= n /\ 0 < n /\ n < 0 /\ n <= 0 /\ p = 0 /\ p = 1 /\ p = 2 /\ p = 3 /\ 0 <= p /\ 0 < p /\ p < 0 /\ p <= 0 /\ q = 0 /\ q = 1 /\ q = 2 /\ q = 3 /\ 0 <= q /\ 0 < q /\ q < 0 /\ q <= 0 /\ r = 0 /\ r = 1 /\ r = 2 /\ r = 3 /\ 0 <= r /\ 0 < r /\ r < 0 /\ r <= 0 /\ tmp = 0 /\ tmp = 1 /\ tmp = 2 /\ tmp = 3 /\ 0 <= tmp /\ 0 < tmp /\ tmp < 0 /\ tmp <= 0 /\ q' = 0 /\ q' = 1 /\ q' = 2 /\ q' = 3 /\ 0 <= q' /\ 0 < q' /\ q' < 0 /\ q' <= 0

-- Γ;p:Peano ⊦ κlet

K = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0
κlet = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0


-- Γ;tmp:{v=Z} ⊦ {v=0} <: K

K = v = 0 /\ 0 <= v /\ v <= 0
κlet = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0

-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K

K = 0 <= v
κlet = v = 0 /\ v = 1 /\ v = 2 /\ v = 3 /\ 0 <= v /\ 0 < v /\ v < 0 /\ v <= 0

-- Γ;tmp:{v=S n};n:{v=n} ⊦ {v=n} <: Peano ✓
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=1} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=q} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=100} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=q'} <: {v/=0} ✓

QUALIFS: {0 <= v, v <= 0,
          1 <= v, v <= 1, 
          2 <= v, v <= 2,
          3 <= v, v <= 3}

vars: {tmp,n,p,q,q',r}


Constraints:

-- Γ ⊦ K
-- Γ;p:Peano ⊦ κlet

-- Γ;tmp:{v=Z} ⊦ {v=0} <: K
-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K

-- Γ;tmp:{v=S n};n:{v=n} ⊦ {v=n} <: Peano
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=1} <: Int
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=q} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=100} <: Int
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=q'} <: {v/=0}

Inital assignment:

K = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= tmp /\ tmp <= 0 /\ 1 <= tmp /\ tmp <= 1 /\ 2 <= tmp /\ tmp <= 2 /\ 3 <= tmp /\ tmp <= 3 /\ 0 <= n /\ n <= 0 /\ 1 <= n /\ n <= 1 /\ 2 <= n /\ n <= 2 /\ 3 <= n /\ n <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3 /\ 0 <= q /\ q <= 0 /\ 1 <= q /\ q <= 1 /\ 2 <= q /\ q <= 2 /\ 3 <= q /\ q <= 3 /\ 0 <= q' /\ q' <= 0 /\ 1 <= q' /\ q' <= 1 /\ 2 <= q' /\ q' <= 2 /\ 3 <= q' /\ q' <= 3 /\ 0 <= r /\ r <= 0 /\ 1 <= r /\ r <= 1 /\ 2 <= r /\ r <= 2 /\ 3 <= r /\ r <= 3
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= tmp /\ tmp <= 0 /\ 1 <= tmp /\ tmp <= 1 /\ 2 <= tmp /\ tmp <= 2 /\ 3 <= tmp /\ tmp <= 3 /\ 0 <= n /\ n <= 0 /\ 1 <= n /\ n <= 1 /\ 2 <= n /\ n <= 2 /\ 3 <= n /\ n <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3 /\ 0 <= q /\ q <= 0 /\ 1 <= q /\ q <= 1 /\ 2 <= q /\ q <= 2 /\ 3 <= q /\ q <= 3 /\ 0 <= q' /\ q' <= 0 /\ 1 <= q' /\ q' <= 1 /\ 2 <= q' /\ q' <= 2 /\ 3 <= q' /\ q' <= 3 /\ 0 <= r /\ r <= 0 /\ 1 <= r /\ r <= 1 /\ 2 <= r /\ r <= 2 /\ 3 <= r /\ r <= 3

-- Γ ⊦ K

K = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= tmp /\ tmp <= 0 /\ 1 <= tmp /\ tmp <= 1 /\ 2 <= tmp /\ tmp <= 2 /\ 3 <= tmp /\ tmp <= 3 /\ 0 <= n /\ n <= 0 /\ 1 <= n /\ n <= 1 /\ 2 <= n /\ n <= 2 /\ 3 <= n /\ n <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3 /\ 0 <= q /\ q <= 0 /\ 1 <= q /\ q <= 1 /\ 2 <= q /\ q <= 2 /\ 3 <= q /\ q <= 3 /\ 0 <= q' /\ q' <= 0 /\ 1 <= q' /\ q' <= 1 /\ 2 <= q' /\ q' <= 2 /\ 3 <= q' /\ q' <= 3 /\ 0 <= r /\ r <= 0 /\ 1 <= r /\ r <= 1 /\ 2 <= r /\ r <= 2 /\ 3 <= r /\ r <= 3

-- Γ;p:Peano ⊦ κlet

K = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3

*** Done with wf constraints

-- Γ;tmp:{v=Z} ⊦ {v=0} <: K

K = 0 <= v /\ v <= 0 /\ v <= 1 /\ v <= 2 /\ v <= 3
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3

-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K

K = 0 <= v /\ v <= 1
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3

-- Γ;tmp:{v=S n};n:{v=n};r:K[tmp:=n] ⊦ {v = 1+r} <: K

K = v <= 1
κlet = 0 <= v /\ v <= 0 /\ 1 <= v /\ v <= 1 /\ 2 <= v /\ v <= 2 /\ 3 <= v /\ v <= 3 /\ 0 <= p /\ p <= 0 /\ 1 <= p /\ p <= 1 /\ 2 <= p /\ p <= 2 /\ 3 <= p /\ p <= 3

-- Γ;tmp:{v=S n};n:{v=n} ⊦ {v=n} <: Peano ✓
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=1} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p] ⊦ {v=q} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=100} <: Int ✓
-- Γ;p:Peano;q:K[tmp:=p];q':{v=1+q} ⊦ {v=q'} <: {v/=0} ✓

-}
