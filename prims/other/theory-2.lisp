
(set-option :print-success false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin Background Theory


(define-sort VarId () Int)
(define-sort BaseId () Int)
(define-sort StrId () Int)
(define-sort FunId () Int)
(define-sort BoxId () Int)
(define-sort HeapId () Int)
(define-sort LocId () Int)

(declare-datatypes ()
  ((DVal (VTrue)
         (VFalse)
         (VInt (VIntSel Int))
         (VStr (VStrSel StrId))
         (VFun (FunSel FunId))
         (empty)                                          ; (VEmpty)
         (upd (ExtBase DVal) (ExtKey DVal) (ExtVal DVal)) ; (VExtend ...)
         (bot)
         (null)
         (undefined) ; added for DJS
)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; uninterpreted System D symbols
;;;;;

(declare-fun hastyp (DVal BoxId) Bool)
(declare-fun heaphas (HeapId LocId DVal) Bool)
(declare-fun heapsel (HeapId LocId DVal) DVal)
(declare-fun packed (DVal) Bool)
(declare-fun len (DVal) DVal)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; tags
;;;;;

(declare-fun tag (DVal) DVal)
(declare-fun TagInt () DVal)
(declare-fun TagBool () DVal)
(declare-fun TagStr () DVal)
(declare-fun TagDict () DVal)
(declare-fun TagFun () DVal)
(declare-fun TagBot () DVal)

; these ids have to match idStrings table in langUtils.ml
(assert (= TagDict  (VStr 1)))
(assert (= TagInt   (VStr 2)))
(assert (= TagBool  (VStr 3)))
(assert (= TagStr   (VStr 4)))
(assert (= TagFun   (VStr 5)))
(assert (= TagBot   (VStr 6)))
(assert (= TagObj   (VStr 7)))
(assert (= TagUndef (VStr 8)))

; no source-level value can be bot
(assert (= (tag bot) TagBot))
(assert (forall ((u BoxId)) (not (hastyp bot u))))

; (assert (forall (v DVal) (= (tag (tag v)) TagStr)))

; NOTE: could define closed set of tags here ...


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level booleans
;;;;;

(assert (= (tag VTrue) TagBool))
(assert (= (tag VFalse) TagBool))

(assert (forall ((v DVal))
                (implies (= (tag v) TagBool)
                         (or (= v VTrue) (= v VFalse)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level integers
;;;;;

(assert (forall ((i Int)) (= (tag (VInt i)) TagInt)))
(assert (forall ((i Int)) (integer (VInt i))))

; TODO 9/24 added wrappers around arithmetic operators
; TODO once these symbols aren't even mentioned when not using integer
;   theory, then move these definitions to logicalmodel-integers.lisp
(declare-fun my_plus (DVal DVal) DVal)
(declare-fun my_minus (DVal DVal) DVal)
(declare-fun my_uminus (DVal) DVal)
(declare-fun my_lt (DVal DVal) Bool)
(declare-fun my_le (DVal DVal) Bool)
(declare-fun my_ge (DVal DVal) Bool)
(declare-fun my_gt (DVal DVal) Bool)

;;;;; NOTE: logicalmodel-int.lisp is conditionally loaded


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level strings
;;;;;

(assert (forall ((i StrId)) (= (tag (VStr i)) TagStr)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level lambdas
;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; other DJS constants
;;;;;

(assert (= (tag null) TagObj))
(assert (= (tag undefined) TagUndef))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level dictionaries
;;;;;

(declare-fun sel (DVal DVal) DVal)

(assert (= (tag empty) TagDict))
(assert (forall ((w1 DVal) (w2 DVal) (w3 DVal))
                (= (tag (upd w1 w2 w3)) TagDict)))

; McCarthy axioms
(assert (forall ((d DVal) (f DVal) (x DVal)) (= (sel (upd d f x) f) x)))
(assert (forall ((d DVal) (f DVal) (x DVal) (g DVal))
                (implies (not (= f g)) (= (sel (upd d f x) g) (sel d g)))))

; default element
(assert (forall ((f DVal)) (= (sel empty f) bot)))


;;;;; End Background Theory
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


