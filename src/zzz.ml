
open Lang
open LangUtils


(* during flow queries, prevents (check-sat) from being indented and prevents
   newline after (push) *)
let doingExtract = ref false

let z3read, z3write, initPipe =
  let (ic, oc) = (ref None, ref None) in
  let z3read () =
    match !ic with
      | Some(f) -> f ()
      | None -> failwith "initPipe() wasn't called" in
  let z3write s =
    match !oc with
      | Some(f) -> f s
      | None -> failwith "initPipe() wasn't called" in
  let initPipe () = (* thunk, since parsing sets mutable vars in Settings *)
    let z3 =
      "z3 -smt2 -in "
        ^ spr "MBQI=%b " false
        ^ spr "SOFT_TIMEOUT=%d " !Settings.zzzTimeout in
    let zin, zout = Unix.open_process z3 in
    let zlog      = open_out (Settings.out_dir ^ "queries.smt2") in
    let reader () = input_line zin in
    let writer s  = fpr zlog "%s" s; flush zlog; fpr zout "%s" s; flush zout in
    ic := Some reader;
    oc := Some writer;
    ()
  in
  (z3read, z3write, initPipe)

let emitPreamble () =
  let rec f ic =
    try z3write (input_line ic ^ "\n"); f ic
    with End_of_file -> () in
  f (open_in (Settings.prim_dir ^ "theory.smt2"));
  if !Settings.bxMode
  then f (open_in (Settings.djs_dir ^ "tests/djs/bx/__bxpreds.smt2"))
  else ()

let dump ?nl:(nl=true) ?tab:(tab=true) s =
  let pre = if tab then indent () else "" in
  let suf = if nl then "\n" else "" in
  z3write (spr "%s%s%s" pre s suf)

let init () =
  initPipe ();
  emitPreamble ();
  ()


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
  pushScope ();
  try
    let x = f () in
    let _ = popScope () in
    x
  with e ->
    let _ = popScope () in (* in case exception is caught later *)
    raise e


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

let wallTime = ref 0.0

let checkSat cap =
  let rec readSat () =
    match z3read () with
      | "sat"     -> "sat", true
      | "unsat"   -> "unsat", false
      | "unknown" -> "unknown", true
      | "success" -> readSat ()
      | s         -> z3err (spr "Zzz.checkSat: read weird string [%s]" s)
  in
  (* Log.log1 "query time %d : " !queryCount; *)
  let (time,(s,b)) = Utils.timeThunk (fun () ->
    (* always print \n after (check-sat), to make sure z3 reads from pipe *)
    dump ~tab:(not !doingExtract) ~nl:true "(check-sat)";
    incr queryCount;
    incrQueryRootCount ();
    readSat ()
  ) in
  wallTime := !wallTime +. time;
  (* Log.log2 "%.2f (%s)\n" time cap; *)
  (* Log.log3 "query time %d : %.2f (%s)\n" !queryCount time cap; *)
  dump (spr "; [%s] query %d (%s)" s !queryCount cap);
  b

let checkSat cap =
  Stats.time "Zzz.checkSat" (fun () -> checkSat cap)

let checkValid cap p =
  pushScope ();
  if p = pFls then () (* dump "(assert true)" *)
  else if !doingExtract then
    dump ~tab:false ~nl:false (spr "(assert (not %s))" (embedForm p))
  else
    dump (spr "(assert (not\n%s  %s))" (indent()) (embedForm p))
  ;
  let sat = checkSat cap in
  popScope ();
  not sat


(***** Adding variables and formulas ******************************************)

let assertFormula f =
  if f <> pTru then
    dump (spr "(assert\n%s  %s)" (indent()) (embedForm (simplify f)))

let addBinding x t =
  dump (spr "(declare-fun %s () DVal) ; depth %d" x !depth);
  dump (spr "(assert (not (= %s bot)))" x);
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

