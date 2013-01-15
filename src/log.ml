
let spr = Printf.sprintf
let fpr = Printf.fprintf

let printToStdout = ref true
let printToLog = ref true
let eagerFlush = ref false

(*******************************************************************************)

let oc_log = open_out (Settings.out_dir ^ "log.txt")

let flushLog () = if !eagerFlush then flush oc_log

let flushStdout () = if !eagerFlush then flush stdout

let log0 s =
  if !printToLog then (fpr oc_log s; flushLog ());
  if !printToStdout then (fpr stdout s; flushStdout ());
  ()

let log1 fmt s1 =
  if !printToLog then (fpr oc_log fmt s1; flushLog ());
  if !printToStdout then (fpr stdout fmt s1; flushStdout ());
  ()

let log2 fmt s1 s2 =
  if !printToLog then (fpr oc_log fmt s1 s2; flushLog ());
  if !printToStdout then (fpr stdout fmt s1 s2; flushStdout ());
  ()

let log3 fmt s1 s2 s3 =
  if !printToLog then (fpr oc_log fmt s1 s2 s3; flushLog ());
  if !printToStdout then (fpr stdout fmt s1 s2 s3; flushStdout ());
  ()

let log4 fmt s1 s2 s3 s4 =
  if !printToLog then (fpr oc_log fmt s1 s2 s3 s4; flushLog ());
  if !printToStdout then (fpr stdout fmt s1 s2 s3 s4; flushStdout ());
  ()

let log5 fmt s1 s2 s3 s4 s5 =
  if !printToLog then (fpr oc_log fmt s1 s2 s3 s4 s5; flushLog ());
  if !printToStdout then (fpr stdout fmt s1 s2 s3 s4 s5; flushStdout ());
  ()

let bigTitle s =
  log1 "%s\n" (String.make 80 ';');
  log1 ";;; %s\n\n" s

let smallTitle s =
  log1 ";;; %s\n\n" s
  
(*******************************************************************************)

let terminate () = flush stdout; exit 1

let printBig cap s =
  log3 "\n%s\n%s\n\n%s\n\n" (String.make 80 '-') cap s

let printErr cap s =
  printBig cap s;
  log1 "%s\n" (Utils.redString cap);
  if not !printToStdout then Printf.printf "%s\n" (Utils.redString cap);
  terminate ()

let printParseErr s = printErr "PARSE ERROR!" s

let printTcErr  l = printErr "TC ERROR!" (String.concat "\n" l)

(*******************************************************************************)

let warn s =
  if !Settings.strictWarn then log1 "\n%s\n" (String.make 80 '-');
  log1 "WARN! %s\n" s;
  if !Settings.strictWarn then printTcErr ["strict warning"]

(*******************************************************************************)

(* TODO should also move other special purpose log files here *)

