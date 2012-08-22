
open Lang
open LangUtils


(* during flow queries, prevents (check-sat) from being indented and prevents
   newline after (push) *)
let doingExtract = ref false

let z3read, z3write =
  (* let zin, zout = Unix.open_process "z3 -smt2 -in" in *)
  (* let zin, zout = Unix.open_process "z3 -smtc SOFT_TIMEOUT=1000 -in" in *)
  (* let zin, zout = Unix.open_process "z3 -smtc -in MBQI=false" in *)
  let zin, zout = Unix.open_process "z3 -smt2 -in MBQI=false" in
  let zlog      = open_out (Settings.out_dir ^ "queries.smt2") in
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
(*
    if !Settings.useTheoryLA
      then f (open_in (Settings.prim_dir ^ "theory-int.smt2"))
      else ()
*)
  end

let dump ?nl:(nl=true) ?tab:(tab=true) s =
  let pre = if tab then indent () else "" in
  let suf = if nl then "\n" else "" in
  z3write (spr "%s%s%s" pre s suf)


(***** Scoping ****************************************************************)

let curVars = Stack.create ()

let _ = Stack.push [] curVars

let varInScope x =
  let b = ref false in
  Stack.iter (fun l -> if List.mem x l then b := true) curVars;
  !b

let pushScope () =
  dump ~nl:(not !doingExtract) "(push) ";
  incr depth;
  Stack.push [] curVars;
  ()

let popScope () =
  decr depth;
  dump "(pop)";
  ignore (Stack.pop curVars);
  ()

let inNewScope f =
  pushScope (); let x = f () in popScope (); x


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
  (* always print \n after (check-sat), to make sure z3 reads from pipe *)
  dump ~tab:(not !doingExtract) ~nl:true "(check-sat)";
  incr queryCount;
  incrQueryRootCount ();
  let (s,b) = readSat () in
  dump (spr "; [%s] query %d (%s)" s !queryCount cap);
  b

let checkSat cap =
  BNstats.time "checkSat" checkSat cap

let checkValid cap p =
  pushScope ();
  (match p with
     | PFls -> dump "(assert true)"
     | _    -> let s = strForm (embedForm p) in
               if !doingExtract
               then dump ~tab:false ~nl:false (spr "(assert (not %s))" s)
               else dump (spr "(assert (not\n%s  %s))" (indent()) s)
  );
  let sat = checkSat cap in
  popScope ();
  not sat

let falseIsProvable cap =
  checkValid (spr "is false provable? %s" cap) PFls


(***** Adding variables and formulas ******************************************)

let assertFormula f =
  if f <> PTru then begin
    let f = removeExtraTrues f in (* TODO why is there still and for 1? *)
    let s = strForm (embedForm f) in
    dump (spr "(assert\n%s  %s)" (indent()) s)
  end

let addBinding x t =
  dump (spr "(declare-fun %s () DVal) ; depth %d" x !depth);
  if varInScope x then Log.warn (spr "already in scope in logic: %s\n" x);
  Stack.push (x :: Stack.pop curVars) curVars;
  assertFormula (applyTyp t (wVar x));
  if Str.string_match (Str.regexp "^end_of_") x 0 then begin
    dump "";
    dump (String.make 80 ';');
    dump (String.make 80 ';');
    dump (String.make 80 ';');
    dump "";
  end;
  ()

