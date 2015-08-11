(!(0<=n) /\ a=0-n || 0<=n /\ a=n) /\ b=a+1 /\ v=b /\ v=0
(declare-const a Int)
(declare-const n Int)
(declare-const v Int)
(declare-const b Bool)

(compute-interpolant
  (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)))
  (and b                                    
    (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)) b (= a (+ n 1)))
    (and (and (=> b (<= 0 n)) (=> (<= 0 n) b)) b (= v (+ n 1))) (= v 0)))
;(not (and b (not (>= n 0))))
