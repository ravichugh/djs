
(******************************************************************************)

(*
let succ :: x:INT -> INT = fun x -> (plus x 1)

let unary_minus :: x:INT -> INT = fun x -> (minus 0 x)
*)

(*
(* 9/18 changed type to match the structure that elimBoolFlag requires *)
(* let neg :: b:BOOL -> {(and (implies (= b true) (= v false))         *)
(*                           (implies (= b false) (= v true)))} =      *)
let neg :: b:BOOL -> {BOOL|(iff (= v true) (= b false))} =
  fun b ->
    if b then false else true
*)

(*
(* TODO change the types of l_and and l_or *)

(* would want these as primitives for evaluation, but doesn't matter for
   type checking *)
let l_and :: b0:BOOL -> b1:BOOL -> {(and (implies (= b0 true) (= v b1))
                                         (implies (= b0 false) (= v false)))} =
  fun b0 b1 ->
    if b0 then b1 else false

let l_or :: b0:BOOL -> b1:BOOL ->
    {BOOL | (iff (= v true) (or (= b0 true) (= b1 true)))} =
  fun b0 b1 ->
    if b0 then true else b1

let le :: x:INT -> y:INT -> BOOL =
  fun x y ->
    l_or (lt x y) (eq x y)
*)


(******************************************************************************)

let end_of_pervasives :: INT = 0

