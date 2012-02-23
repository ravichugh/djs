
let pr = Printf.printf
let fpr = Printf.fprintf

let oc_log = open_out "out/log.lisp"

let bigTitle s =
  fpr oc_log "%s\n" (String.make 80 ';');
  fpr oc_log ";;; %s\n\n" s

let smallTitle s =
  fpr oc_log ";;; %s\n\n" s

let log s =
  fpr oc_log "%s\n" s
  
let warn s =
  if !Settings.strictWarn then pr "\n%s\n" (String.make 80 '-');
  pr "WARN! %s\n" s;
  if !Settings.strictWarn then LangUtils.printTcErr ["strict warning"]

