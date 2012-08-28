
(set-option :print-success false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin Background Theory


(define-sort IntId   () Int)
(define-sort StrId   () Int)
(define-sort FunId   () Int)
(define-sort BoxId   () Int)
(define-sort HeapId  () Int)
(define-sort LocId   () Int)

(declare-datatypes () (
  (DVal  (VTrue)
         (VFalse)
         (VInt (VIntSel IntId))
         (VStr (VStrSel StrId))
         (VFun (FunSel FunId))
         (empty)                                          ; (VEmpty)
         (upd (ExtBase DVal) (ExtKey DVal) (ExtVal DVal)) ; (VExtend ...)
         (bot)
         (null)
         (undefined)
         (VRef (VRefSel Int))
         (VObjRef (VObjRefSel Int)) ; 4/1
  )
))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; uninterpreted System !D symbols
;;;;;

(declare-fun hastyp  (DVal BoxId) Bool)
(declare-fun heaphas (HeapId LocId DVal) Bool)
(declare-fun heapsel (HeapId LocId DVal) DVal)
(declare-fun packed  (DVal) Bool)
(declare-fun len     (DVal) DVal)
(declare-fun integer (DVal) Bool)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; tags
;;;;;

(declare-fun tag (DVal) DVal)

; the following integer ids have to match idStrings table in langUtils.ml
(declare-fun TagDict    () DVal) (assert (= TagDict    (VStr 1)))
(declare-fun TagNum     () DVal) (assert (= TagNum     (VStr 2)))
(declare-fun TagBool    () DVal) (assert (= TagBool    (VStr 3)))
(declare-fun TagStr     () DVal) (assert (= TagStr     (VStr 4)))
(declare-fun TagFun     () DVal) (assert (= TagFun     (VStr 5)))
(declare-fun TagBot     () DVal) (assert (= TagBot     (VStr 6)))
(declare-fun TagObj     () DVal) (assert (= TagObj     (VStr 7)))
(declare-fun TagUndef   () DVal) (assert (= TagUndef   (VStr 8)))
(declare-fun TagRef     () DVal) (assert (= TagRef     (VStr 9)))

(assert                     (= (tag VTrue)        TagBool))
(assert                     (= (tag VFalse)       TagBool))
(assert                     (= (tag bot)          TagBot))
(assert                     (= (tag null)         TagObj))
(assert                     (= (tag undefined)    TagUndef))
(assert (forall ((i IntId)) (= (tag (VInt i))     TagNum)))
(assert (forall ((i StrId)) (= (tag (VStr i))     TagStr)))
(assert (forall ((i FunId)) (= (tag (VFun i))     TagFun)))
(assert (forall ((i Int))   (= (tag (VRef i))     TagRef))) ; 3/12
(assert (forall ((i Int))   (= (tag (VObjRef i))  TagObj))) ; 4/1

(assert (= (tag empty) TagDict))
(assert (forall ((w1 DVal) (w2 DVal) (w3 DVal))
        (= (tag (upd w1 w2 w3)) TagDict)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; booleans
;;;;;

(assert (forall ((v DVal))
                (implies (= (tag v) TagBool)
                         (or (= v VTrue) (= v VFalse)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; dictionaries
;;;;;

(declare-fun sel (DVal DVal) DVal)

; McCarthy axioms
(assert (forall ((d DVal) (f DVal) (x DVal)) (= (sel (upd d f x) f) x)))
(assert (forall ((d DVal) (f DVal) (x DVal) (g DVal))
                (implies (not (= f g)) (= (sel (upd d f x) g) (sel d g)))))

; default element
(assert (forall ((f DVal)) (= (sel empty f) bot)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; numbers
;;;;;

(declare-fun l_uminus (DVal) DVal)
(declare-fun l_minus  (DVal DVal) DVal)
(declare-fun l_plus   (DVal DVal) DVal)
(declare-fun l_lt     (DVal DVal) Bool)
(declare-fun l_le     (DVal DVal) Bool)
(declare-fun l_ge     (DVal DVal) Bool)
(declare-fun l_gt     (DVal DVal) Bool)

(assert (forall ((w1 DVal) (w2 DVal))
        (and
           (= (<  (VIntSel w1) (VIntSel w2)) (l_lt w1 w2))
           (= (<= (VIntSel w1) (VIntSel w2)) (l_le w1 w2))
           (= (>= (VIntSel w1) (VIntSel w2)) (l_ge w1 w2))
           (= (>  (VIntSel w1) (VIntSel w2)) (l_gt w1 w2))
        )))

; TODO all these needed? need other axioms?
(assert (forall ((w1 DVal) (w2 DVal))
        (and
           (= (l_le w1 w2) (not (l_gt w1 w2)))
           (= (l_ge w1 w2) (not (l_lt w1 w2)))
           (= (l_le w1 w2) (or (l_lt w1 w2) (= w1 w2)))
           (= (l_ge w1 w2) (or (l_gt w1 w2) (= w1 w2)))
        )))

(assert (forall ((w1 DVal) (w2 DVal) (w3 DVal))
        (= (= w1 (l_plus w2 w3))
           (= (VIntSel w1) (+ (VIntSel w2) (VIntSel w3))))))

(assert (forall ((w1 DVal) (w2 DVal) (w3 DVal))
        (= (= w1 (l_minus w2 w3))
           (= (VIntSel w1) (- (VIntSel w2) (VIntSel w3))))))

(assert (forall ((w1 DVal) (w2 DVal))
        (= (= w1 (l_uminus w2))
           (= (VIntSel w1) (~ (VIntSel w2))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; bot, null, undefined
;;;;;

; no source-level function value can be bot
(assert (forall ((u BoxId)) (not (hastyp bot u))))

; 3/15
; could either store let __null = null in initial typing environment, or
; assert null :: Null here. make sure the id 1 is assigned to box UNull in
; langUtils.ml.
(assert (hastyp null 1))

; 3/5
(assert (forall ((u BoxId)) (not (hastyp undefined u))))


;;;;; End Background Theory
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

