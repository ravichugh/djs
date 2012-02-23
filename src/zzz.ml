
open Lang
open LangUtils

let doingExtract = ref false

let z3read, z3write =
  let zin, zout = Unix.open_process "z3 -smt2 -in" in
  let zlog      = open_out "out/queries.lisp" in
  let reader () = input_line zin in
  let writer s  = fpr zlog "%s" s; flush zlog; fpr zout "%s" s; flush zout in
    (reader, writer)

let emitPreamble () =
  let rec f ic =
    try z3write (input_line ic ^ "\n"); f ic
    with End_of_file -> ()
  in
  f (open_in "theory.lisp");
  if !Settings.useTheoryLA then f (open_in "theory-int.lisp");
  ()

(* let _ = emitPreamble () *)

let dump ?nl:(nl=true) ?tab:(tab=true) s =
  let pre = if tab then indent () else "" in
  let suf = if nl then "\n" else "" in
  z3write (spr "%s%s%s" pre s suf)

let pushScope () =
  dump ~nl:(not !doingExtract) "(push) ";
  incr depth;
  ()

let popScope () =
  decr depth;
  dump "(pop)";
  ()


(***** Querying ***************************************************************)

(* prevents (check-sat) from being indented during flow queries *)
let doingCheckFlow = ref false

let queryCount = ref 0

let checkSat cap =
  let rec readSat () =
    match z3read () with
      | "sat"     -> "sat", true
      | "unsat"   -> "unsat", false
      | "unknown" -> "unknown", true
      | "success" -> readSat ()
      | s         -> z3err (spr "SAT check read weird string [%s]" s)
  in
  let b = if !doingCheckFlow then false else true in
  dump ~tab:b ~nl:false "(check-sat)";
  incr queryCount;
  let (s,b) = readSat () in
  dump ~tab:false (spr "; [%s] query %d (%s)" s !queryCount cap);
  b

let checkValid cap p =
  pushScope ();
  (match p with
     | PFls -> dump "(assert true)"
     | _    -> let s = strForm (embedForm p) in
               if !doingExtract
               then dump ~tab:false (spr "(assert (not %s))" s)
               else dump (spr "(assert (not\n%s  %s))" (indent()) s)
  );
  let sat = checkSat cap in
  popScope ();
  not sat

let falseIsProvable cap =
  checkValid (spr "is false provable? %s" cap) PFls


(***** Adding/removing bindings ***********************************************)

let curScope = ref []

let addBinding ?isNew:(isNew=true) x f =
  let sort = "DVal" in
  if isNew then begin
    dump (spr "(declare-funs ((%s %s))) ; depth %d" x sort !depth);
    if List.mem x !curScope then
      Log.warn (spr "already in scope in logic: %s\n" x);
    curScope := x::!curScope;
  end;
  if f <> PTru then
    let s = strForm (embedForm f) in
    dump (spr "(assert\n%s  %s)" (indent()) s)
  else
    ()

let removeBinding () =
  try curScope := List.tl !curScope
  with Failure("tl") -> Log.warn "why is curScope empty?\n"

let addTypeVar x =
  dump (spr "(declare-preds ((%s DVal))) ; %d" x !depth);
  curScope := x::!curScope;
  ()


(***** Public push/pop ********************************************************)

(* TODO move the tcUtils versions in here, so that tc doesn't have
   to push/pop *)

let assertFormula f = let s = strForm (embedForm f) in
                      dump (spr "(assert\n%s  %s)" (indent()) s)

let pushForm f      = pushScope (); assertFormula f
let popForm ()      = popScope ()

let pushBinding x f = pushScope (); addBinding x f
let popBinding ()   = removeBinding (); popScope ()


