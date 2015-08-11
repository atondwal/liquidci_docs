Constraint Generation
=====================

I fixed the alpha-renaming and added the well-formedness constraints in
the three examples for Step 1 (constraint generation), attached. Does
this look right?

Solving for kvars
=================

I'm a little confused about your comments regarding Step 2 (Solving for
kvars). Do you want to me to show more work solving for kvars, or were
you referring to Step 3 (Craig interpolants)? As far as I can tell,
the algorithm for finding kvars is just building the conjunction of all
the possible qualifiers, with all possible substitutions and then
filtering out the ones that don't work.

Craig Interpolants
==================

I'm still having trouble putting together a set of examples I'm happy
with, but here's what I'm thinking so far:

-   These three examples aren't examples of what I was thinking of wrt
    Craig interpolation to suggest changes to invariants; we'd need to
    already have the free variables in the propositions, so if we took
    out the qualifiers, we'd have nothing to work with. My intuition is
    that this technique would work well for programs like those that
    GenProg does well on: in Wesspeak, those that "contain the seeds of
    their own repair." This is what I mentioned briefly earlier, and I
    detail more at the end of this email. **If you had something else in
    mind, I'd be grateful to know what.**
-   Two prototyical types of programs where I think that Craig
    interpolation would be useful is the one I mentioned about (which I
    will clarify below) and programs with very redundant propositions.
    The first technique should do well in eliminating redundant
    propositions, while the second technique that I mentioned before
    might be able to suggest invariants for larger programs


Redundant Propositions
----------------------

Suppose we have `x`, with invariants `0 <= x /\ 3 <= x`. To the user, we
probably never want to report both of these redundant invariants.
Instead, we want to just say `0 <= x`. (I can see us maybe wanting us to
specify both invariants if we want to find *all* the sources of conflict
for that one step of type inference, but for a conflict with `x /= 0`,
for example, we certainly don't need to see both) That, I think, will
cut down on the length on a lot of the longer error messages in the LH
negative test suite.Note that, since I'm evaluating the entirety of the
expression, this would cut down, not only on the number of propositions
we're showing the user that give no new information, but also those that
don't give relevant information, so that we go from the unsatisfiable
`x <= 0 /\ x /= 5 -> x /= 0` to `x <= 0 -> x /= 0`.

Here's the simple example I have have so far.

``` {.haskell liquid="/tmp/Reduce.hs"}
module Reduce (run) where

g :: Int -> Int -> Int
g a x = if x < a then a else x

run x = div 1 ((g 3 $ g 1 x) - 4)
```

This gives the error:

``` {.haskell}
  Reduce_simple.hs:6:16-32: Error: Liquid Type Mismatch
    Inferred type
      VV : Int | VV == ?c && VV == ?g - ?f
   
    not a subtype of Required type
      VV : Int | VV /= 0
   
    In Context
      ?e : Int | ?e > 0 && ?e >= x && ?e >= ?a
      ?a : Int | ?a == (1  :  int)
      ?c : Int | ?c == ?g - ?f
      x  : Int
      ?b : Int | ?b == (1  :  int)
      ?d : Int | ?d == (3  :  int)
      ?f : Int | ?f == (4  :  int)
      ?g : Int | ?g > 0 && ?g > ?a && ?g > ?b && ?g >= ?e && ?g >= x && ?g >= ?d
```

Now let `q := VV == 0 \/ VV /= 0 \/ ?g == 0` and
`p := ?e > 0 && ?e >= x && ?e >= ?a /\ ?a == (1  :  int) /\ ?c == ?g - ?f /\ /\ ?b == (1  :  int) /\ ?d == (3  :  int) /\ ?f == (4  :  int) /\ ?g > 0 && ?g > ?a && ?g > ?b && ?g >= ?e && ?g >= x && ?g >= ?d /\ VV : Int | VV == ?c && VV == ?g - ?f -> VV /= 0`
(assume we are not treating constants as propositional variables here. I
have some thoughts/questions/confusions about constants as propositional
variables below, but even if we were treating them as propositional
variables in the case below, it shouldn't matter on the level of the SMT
solver)

Then, `interpolate p q` should give us something equivalent to
`VV /= ?g - 4 /\ g >= 3 -> VV /= 0`, which is a much simpler error
message than the one above. **Admittedly, it seems like we're likely to
get out something written more like `VV /=0 \/ VV /= ?g - 4 \/ g < 3`,
and I'm not sure if that's true or how to get that into a form that's
more human-readable.**

I had a couple of troubles while trying to build this example (and
working towards a more motivating one), see section 4.

Clearing up the previously mentioned method
-------------------------------------------

(While typing this out, I noticed a mistake with all the nots, and I
don't think this part works anymore, oops, sorry.)

Other Concerns
========

Constants
---------

So the first thing I tried to write is

``` {.haskell liquid="/tmp/Reduce_infer.hs"}
module Reduce (run) where

g :: Int -> Int
g x = if x < 3 then 3 else x

run x = div 1 ((g x) - 2)
```

Which fails to typecheck with the error

``` {.haskell}
 Reduce_infer.hs:6:16-23: Error: Liquid Type Mismatch
   Inferred type
     VV : Int | VV == ?b && VV == ?a - ?c
  
   not a subtype of Required type
     VV : Int | VV /= 0
  
   In Context
     ?a : Int | ?a > 0 && ?a >= x
     ?c : Int | ?c == (2  :  int)
     x  : Int
     ?b : Int | ?b == ?a - ?c
```

which caught me off guard, since we have `* <= v` as a qualifier. Sure
enough, putting in the refinement by hand does it

``` {.haskell liquid="/tmp/Reduce_inv.hs"}
module Reduce (run) where

{-@ g :: Int -> {v:Int | v >= 3} @-}
g :: Int -> Int
g x = if x < 3 then  3 else x

run x = div 1 ((g x) - 2)
```

but working off an already-there refinement gives us much less room to
play the role of coming up with them, so I wanted to figure out why this
was happening. After some playing around, I got it to infer the type if
we parameterize over 3, rather than put it in directly.

``` {.haskell liquid="/tmp/Reduce_para.hs"}
module Reduce (run) where

g :: Int -> Int -> Int
g a x = if x < a then a else x

run x = div 1 ((g 3 x) - 2)
```

This seems to imply that the problem is that we aren't seeing the `3` as
a propositional variable to test. Uncurrying confirms:

``` {.haskell liquid="/tmp/Reduce_h.hs"}
module Reduce (run) where

g :: Int -> Int -> Int
g a x = if x < a then a else x
h = g 3

run x = div 1 ((h x)- 2)
```

``` {.haskell}
/home/atondwal/0-research/weimer/errors/Reduce_intermediate.hs:7:16-24: Error: Liquid Type Mismatch
 Inferred type
   VV : Int | VV == ?b && VV == ?c - ?a

 not a subtype of Required type
   VV : Int | VV /= 0

 In Context
   ?a : Int | ?a == (2  :  int)
   ?c : Int | ?c > 0 && ?c >= x
   x  : Int
   ?b : Int | ?b == ?c - ?a
```

**So why aren't we picking up constants in the program and putting them in
with variables?** Is it too costly? We're exponential in the number of
variables, but I don't think that we have enough constants that it would
result in a substantial slowdown. If it does, can we put in a second
run, if the original fails to typecheck?

`undefined`
-----------

While we're on the topic, I was surprised to learn that `undefined`
doesn't have a bottom type. And I was unable to give it one. This was my
best try

``` {.haskell}
import Prelude hiding (undefined)
import qualified GHC.Err as E

{- undefined :: { v : a | 1 = 0 } -}
undefined = E.undefined

main = undefined
```

Is this because GHC just strips out any code with a value of undefined?
It seems like being able to get this information, and/or have liquid
type inference treat unmatched pattern matches as branches to do
inference would be useful, say, to be able to **straightforwardly write
the `assert` function without having to write out the refinements. Am I
just doing something wrong here?**

``` {.haskell}
module Assert (myAssert) where

myAssert True = ()
myAssert _ = error "Assertion Failed"
```

Checking the types, `myAssert :: GHC.Types.Bool -> ()`.

Invariants for vanilla haskell
------------------------------

This seems like a pattern that's pretty common in vanilla (non-liquid)
haskell, and since it's not implemented yet, I think combining the
approaches here would make for a rather impressive result, where we'd be
able to infer a bunch of invariants in haskell, and then give
informative error messages on why regular haskell code is broken.

