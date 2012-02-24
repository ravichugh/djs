
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
  (DVal  (True)
         (False)
         (VInt (VIntSel Int))
         (VStr (VStrSel StrId))
         (VFun (FunSel FunId))
         (empty)                                          ; (VEmpty)
         (upd (ExtBase DVal) (ExtKey DVal) (ExtVal DVal)) ; (VExtend ...)
         (bot)
         (null)
         (undefined) ; added for DJS
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; tags
;;;;;

(declare-fun tag (DVal) DVal)
(declare-funs
  ((TagInt DVal) (TagBool DVal) (TagStr DVal) (TagDict DVal)
   (TagFun DVal)
   (TagBot DVal)))

; these ids have to match idStrings table in langUtils.ml
(assert (= TagInt  (VStr 1)))
(assert (= TagBool (VStr 2)))
(assert (= TagStr  (VStr 3)))
(assert (= TagDict (VStr 4)))
(assert (= TagFun  (VStr 5)))
(assert (= TagBot  (VStr 6)))

; no source-level value can be bot
(assert (= (tag bot) TagBot))
(assert (forall (u BoxId) (not (hastyp bot u))))

; (assert (forall (v DVal) (= (tag (tag v)) TagStr)))

; NOTE: could define closed set of tags here ...


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level booleans
;;;;;

(assert (= (tag True) TagBool))
(assert (= (tag False) TagBool))

(assert (forall (v DVal)
                (implies (= (tag v) TagBool)
                         (or (= v True) (= v False)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; source-level integers
;;;;;

(assert (forall (i Int) (= (tag (VInt i)) TagInt)))

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


