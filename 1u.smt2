(declare-const a Int)
(declare-const n Int)
(declare-const v Int)
(declare-const b Bool)
(compute-interpolant
  (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)) b (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)) b (= a (+ n 1))) (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)) b (= v (+ n 1)))) (= v 0))
;unsat
;(<= 1 v)
