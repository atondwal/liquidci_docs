;depth = 1
(declare-sort A)
(declare-const q_ Int)
(declare-const q Int)
(declare-const r Int)
(declare-const v Int)
(declare-const p A)
(declare-const n A)
(declare-const Z A)
(declare-fun S (A) A)
(compute-interpolant
( and
  (= v q_)
  (= q_ (+ q 1))
  (or 
    (and (= p Z) (= q 0))
    (and
    (= p (S n))
    (= n Z)
    (= r 0)
    (= q (+ 1 r))
    )
  )
)
(= v 0)
)
;unsat
;(not (= 0 v))
