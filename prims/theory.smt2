
(set-option :print-success false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Begin Background Theory


(define-sorts (
  (VarId Int)
  (BaseId Int)
  (StrId Int)
  (FunId Int)
  (BoxId Int)
  (HeapId Int)
  (LocId Int)
))

(declare-datatypes (
  (DVal  (VTrue)
         (VFalse)
         (VInt (VIntSel Int))
         (VStr (VStrSel StrId))
         (VFun (FunSel FunId))
         (empty)                                          ; (VEmpty)
         (upd (ExtBase DVal) (ExtKey DVal) (ExtVal DVal)) ; (VExtend ...)
         (bot)
         (null)
         (undefined) ; added for DJS
         (VRef (VRefSel Int))
         ;(VArray (VArraySel Int))
         (VNewObjRef (VNewObjRefSel Int)) ; 4/1
  )
))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; uninterpreted System D symbols
;;;;;

(declare-preds ((hastyp DVal BoxId)))
(declare-preds ((heaphas HeapId LocId DVal)))
(declare-fun heapsel (HeapId LocId DVal) DVal)
(declare-preds ((packed DVal)))
(declare-fun len (DVal) DVal)
(declare-preds ((integer DVal)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; tags
;;;;;

(declare-fun tag (DVal) DVal)
(declare-funs
  ((TagNum DVal) (TagBool DVal) (TagStr DVal) (TagDict DVal)
   (TagFun DVal) (TagBot DVal)
   (TagObj DVal) (TagUndef DVal)
   (TagRef DVal) (TagArray DVal)))

; these ids have to match idStrings table in langUtils.ml
(assert (= TagDict  (VStr 1)))
(assert (= TagNum   (VStr 2)))
(assert (= TagBool  (VStr 3)))
(assert (= TagStr   (VStr 4)))
(assert (= TagFun   (VStr 5)))
(assert (= TagBot   (VStr 6)))
(assert (= TagObj   (VStr 7)))
(assert (= TagUndef (VStr 8)))
(assert (= TagRef   (VStr 9)))
; (assert (= TagArray (VStr 10)))

; NOTE: could define closed set of tags here ...


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; logical bot
;;;;;

(assert (= (tag bot) TagBot))

; no source-level function value can be bot
(assert (forall (u BoxId) (not (hastyp bot u))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level booleans
;;;;;

(assert (= (tag VTrue) TagBool))
(assert (= (tag VFalse) TagBool))

(assert (forall (v DVal)
                (implies (= (tag v) TagBool)
                         (or (= v VTrue) (= v VFalse)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level numbers
;;;;;

(assert (forall (i Int) (= (tag (VInt i)) TagNum)))
; 4/1 removed this, because don't want the skolemized ones to be integer
;(assert (forall (i Int) (integer (VInt i))))

; TODO 9/24 added wrappers around arithmetic operators
; TODO once these symbols aren't even mentioned when not using integer
;   theory, then move these definitions to logicalmodel-integers.lisp
(declare-fun my_plus (DVal DVal) DVal)
(declare-fun my_minus (DVal DVal) DVal)
(declare-fun my_uminus (DVal) DVal)
(declare-preds
   ((my_lt DVal DVal) (my_le DVal DVal) (my_ge DVal DVal) (my_gt DVal DVal)))

;;;;; NOTE: logicalmodel-int.lisp is conditionally loaded


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level strings
;;;;;

(assert (forall (i StrId) (= (tag (VStr i)) TagStr)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level lambdas
;;;;;

(assert (forall (i Int) (= (tag (VFun i)) TagFun)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; other DJS constants
;;;;;

(assert (= (tag null) TagObj))
(assert (= (tag undefined) TagUndef))

; 3/15
; could either store let __null = null in initial typing environment, or
; assert null :: Null here. make sure the id 1 is assigned to box UNull in
; langUtils.ml.
(assert (hastyp null 1))

; 3/5
(assert (forall (u BoxId) (not (hastyp undefined u))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level reference values
;;;;;

; 3/12
(assert (forall (i Int) (= (tag (VRef i)) TagRef)))

; 4/1
(assert (forall (i Int) (= (tag (VNewObjRef i)) TagObj)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; functional array values
;;;;;

;; 3/13
;(assert (forall (i Int) (= (tag (VArray i)) TagArray)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level dictionaries
;;;;;

(declare-fun sel (DVal DVal) DVal)

(assert (= (tag empty) TagDict))
(assert (forall (w1 DVal) (w2 DVal) (w3 DVal)
                (= (tag (upd w1 w2 w3)) TagDict)))

; McCarthy axioms
(assert (forall (d DVal) (f DVal) (x DVal) (= (sel (upd d f x) f) x)))
(assert (forall (d DVal) (f DVal) (x DVal) (g DVal)
                (implies (not (= f g)) (= (sel (upd d f x) g) (sel d g)))))

; default element
(assert (forall (f DVal) (= (sel empty f) bot)))


;;;;; End Background Theory
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


