
(******************************************************************************)

(* TODO only use + if can var elim *)
(*
let succ :: x:INT -> {INT|(= v (+ x 1))} = fun x -> plus x 1
*)
let succ :: x:INT -> INT = fun x -> (plus x 1)

let unary_minus :: x:INT -> INT = fun x -> (minus 0 x)

(*
(* 9/18 changed type to match the structure that elimBoolFlag requires *)
(* let neg :: b:BOOL -> {(and (implies (= b True) (= v False))         *)
(*                           (implies (= b False) (= v True)))} =      *)
let neg :: b:BOOL -> {BOOL|(iff (= v True) (= b False))} =
  fun b ->
    if b then False else True
*)

(*
(* TODO change the types of l_and and l_or *)

(* would want these as primitives for evaluation, but doesn't matter for
   type checking *)
let l_and :: b0:BOOL -> b1:BOOL -> {(and (implies (= b0 True) (= v b1))
                                         (implies (= b0 False) (= v False)))} =
  fun b0 b1 ->
    if b0 then b1 else False

let l_or :: b0:BOOL -> b1:BOOL ->
    {BOOL | (iff (= v True) (or (= b0 True) (= b1 True)))} =
  fun b0 b1 ->
    if b0 then True else b1

let le :: x:INT -> y:INT -> BOOL =
  fun x y ->
    l_or (lt x y) (eq x y)
*)


(******************************************************************************)

let end_of_pervasives :: INT = 0

