
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin Integer Wrapper Axioms

; TODO iff instead of implies?
(assert (forall ((w1 DVal) (w2 DVal))
        (and
           (iff (<  (VIntSel w1) (VIntSel w2)) (my_lt w1 w2))
           (iff (<= (VIntSel w1) (VIntSel w2)) (my_le w1 w2))
           (iff (>= (VIntSel w1) (VIntSel w2)) (my_ge w1 w2))
           (iff (>  (VIntSel w1) (VIntSel w2)) (my_gt w1 w2))
        )))

; TODO all these needed? need other axioms?
(assert (forall ((w1 DVal) (w2 DVal))
        (and
           (iff (my_le w1 w2) (not (my_gt w1 w2)))
           (iff (my_ge w1 w2) (not (my_lt w1 w2)))
           (iff (my_le w1 w2) (or (my_lt w1 w2) (= w1 w2)))
           (iff (my_ge w1 w2) (or (my_gt w1 w2) (= w1 w2)))
        )))

(assert (forall (w1 DVal) (w2 DVal) (w3 DVal)
        (iff (= w1 (my_plus w2 w3))
             (= (VIntSel w1) (+ (VIntSel w2) (VIntSel w3))))))

(assert (forall (w1 DVal) (w2 DVal) (w3 DVal)
        (iff (= w1 (my_minus w2 w3))
             (= (VIntSel w1) (- (VIntSel w2) (VIntSel w3))))))

; TODO what is syntax for ~ in smt2?
; (assert (forall (w1 DVal) (w2 DVal)
;         (iff (= w1 (my_uminus w2))
;              (= (VIntSel w1) (~ (VIntSel w2))))))



;;;;; End Integer Wrapper Axioms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

