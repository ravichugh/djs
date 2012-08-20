
open Lang
open LangUtils

let doingExtract = ref false

let z3read, z3write =
  (* let zin, zout = Unix.open_process "z3 -smt2 -in" in *)
  (* let zin, zout = Unix.open_process "z3 -smtc SOFT_TIMEOUT=1000 -in" in *)
  let zin, zout = Unix.open_process "z3 -smtc -in MBQI=false" in
  let zlog      = open_out (Settings.out_dir ^ "queries.smtc") in
  let reader () = input_line zin in
  let writer s  = fpr zlog "%s" s; flush zlog; fpr zout "%s" s; flush zout in
    (reader, writer)

let emitPreamble () =
  let rec f ic =
    try z3write (input_line ic ^ "\n"); f ic
    with End_of_file -> ()
  in
  if !Settings.marshalInEnv then
    f (open_in (Settings.out_dir ^ "env.lisp"))
  else begin
    f (open_in (Settings.prim_dir ^ "theory.smt2"));
    if !Settings.useTheoryLA
      then f (open_in (Settings.prim_dir ^ "theory-int.smt2"))
      else ()
  end

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


(***** Stats ******************************************************************)

let queryRoot = ref "none"

let queryRootCount = Hashtbl.create 17

let incrQueryRootCount () =
  let reason = !queryRoot in
  let c = if Hashtbl.mem queryRootCount reason
            then 1 + Hashtbl.find queryRootCount reason
            else 1 in
  Hashtbl.replace queryRootCount reason c

let writeQueryStats () =
  let oc = open_out (Settings.out_dir ^ "query-stats.txt") in
  Hashtbl.iter (fun s i -> fpr oc "%-10s %10d\n" s i) queryRootCount


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
  incrQueryRootCount ();
  let (s,b) = readSat () in
  dump ~tab:false (spr "; [%s] query %d (%s)" s !queryCount cap);
  b

let checkSat cap =
  BNstats.time "checkSat" checkSat cap

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
    (* dump (spr "(declare-funs ((%s %s))) ; depth %d" x sort !depth); *)
    dump (spr "(declare-fun %s () %s) ; depth %d" x sort !depth);
    if List.mem x !curScope then
      Log.warn (spr "already in scope in logic: %s\n" x);
    curScope := x::!curScope;
  end;
  if f <> PTru then begin
    let f = removeExtraTrues f in (* TODO why is there still and for 1? *)
    let s = strForm (embedForm f) in
    dump (spr "(assert\n%s  %s)" (indent()) s)
  end;
  if Str.string_match (Str.regexp "^end_of_") x 0 then begin
    dump "";
    dump (String.make 80 ';');
    dump (String.make 80 ';');
    dump (String.make 80 ';');
    dump "";
  end;
  ()

let removeBinding () =
  try curScope := List.tl !curScope
  with Failure("tl") -> Log.warn "why is curScope empty?\n"


(***** Public push/pop ********************************************************)

(* TODO move the tcUtils versions in here, so that tc doesn't have
   to push/pop *)

let assertFormula f = let s = strForm (embedForm f) in
                      dump (spr "(assert\n%s  %s)" (indent()) s)

let pushForm f      = pushScope (); assertFormula f
let popForm ()      = popScope ()

let pushBinding x f = pushScope (); addBinding x f
let popBinding ()   = removeBinding (); popScope ()


