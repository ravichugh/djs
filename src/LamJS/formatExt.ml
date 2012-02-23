open Format

type printer = formatter -> unit
 
let nest (p : printer) (fmt : formatter) : unit =
  pp_open_vbox fmt 2;
  p fmt;
  pp_close_box fmt ()
 
let rec sep (lst : printer list) (fmt : formatter) : unit = match lst with
    x1 :: x2 :: xs' ->
      pp_open_box fmt 2;
      x1 fmt; 
      pp_close_box fmt ();
      pp_print_space fmt (); 
      sep (x2 :: xs') fmt
  | [x] -> 
      pp_open_box fmt 2;
      x fmt;
      pp_close_box fmt ()
  | [] -> ()

let rec squish (lst : printer list) (fmt : formatter) : unit = match lst with
  | x :: xs -> x fmt; squish xs fmt
  | [] -> ()
 
 
let vert (p : printer list) (fmt : formatter) : unit = 
  pp_open_vbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()
 
let horz (p : printer list) (fmt : formatter) : unit = 
  pp_open_hbox fmt ();
  sep p fmt;
  pp_close_box fmt ()
  
let text s fmt = pp_print_string fmt s
 
let int n fmt = pp_print_int fmt n
 
let enclose l r (inner : printer) (fmt : formatter) = 
  pp_open_box fmt 2;
  pp_print_string fmt l;
  inner fmt;
  pp_print_string fmt r;
  pp_close_box fmt ()
 
let parens = enclose "(" ")"
 
let braces = enclose "{" "}"
 
let brackets = enclose "[" "]"

let angles = enclose "<" ">"

let to_string (f : 'a -> printer) (x : 'a) : string  =
  f x str_formatter;
  flush_str_formatter ()
