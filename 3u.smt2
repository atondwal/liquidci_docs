(declare-const a Int)
(declare-const n Int)
(declare-const m Int)
(declare-const v Int)
(declare-const c Int)
(declare-const c_ Int)
(declare-const b Int)
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b0_ Bool)
(declare-const b1_ Bool)
(declare-const b2_ Bool)
(declare-const b3_ Bool)
(compute-interpolant
( and
  (= b3 (<= 0 n))
  (= b2 (<= 0 n))
  ( and
    (= b0 (<= 0 n))
    (not b0)
    (or (= a (- n)) (= b1 (= 0 n)))
    b1
    (= a n)
  )
  (= b3_ (<= 0 m))
  (= b2_ (<= 0 m))
  ( and
    (= b0_ (<= 0 m))
    (not b0_)
    (or (= b (- m) (= b1_ (<= 0 m))))
    b1_
    (= b m)
  )
  (= c_ (+ b 1))
  (= c (+ a c_))
  (= v c)
)
  (= v 0)
)
;unsat
;(not (= 0 v))
