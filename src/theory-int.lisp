
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin Integer Wrapper Axioms

; TODO iff instead of implies?
(assert (forall (w1 DVal) (w2 DVal)
        (and
           (iff (<  (VIntSel w1) (VIntSel w2)) (my_lt w1 w2))
           (iff (<= (VIntSel w1) (VIntSel w2)) (my_le w1 w2))
           (iff (>= (VIntSel w1) (VIntSel w2)) (my_ge w1 w2))
           (iff (>  (VIntSel w1) (VIntSel w2)) (my_gt w1 w2))
        )))

; TODO all these needed? need other axioms?
(assert (forall (w1 DVal) (w2 DVal)
        (and
           (iff (my_le w1 w2) (not (my_gt w1 w2)))
           (iff (my_ge w1 w2) (not (my_lt w1 w2)))
           (iff (my_le w1 w2) (or (my_lt w1 w2) (= w1 w2)))
           (iff (my_ge w1 w2) (or (my_gt w1 w2) (= w1 w2)))
        )))

(assert (forall (i Int) (j Int) (k Int)
        (iff (= i (+ j k)) (= (VInt i) (my_plus (VInt j) (VInt k))))))

(assert (forall (i Int) (j Int) (k Int)
        (iff (= i (- j k)) (= (VInt i) (my_minus (VInt j) (VInt k))))))

(assert (forall (i Int) (j Int)
        (iff (= i (~j)) (= (VInt i) (my_uminus (VInt j))))))


;;;;; End Integer Wrapper Axioms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

