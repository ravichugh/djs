

module IntMap =
  Map.Make (struct type t = int let compare = compare end)


module StrMap =
  Map.Make (struct type t = string let compare = compare end)


module StrSet =
  Set.Make (struct type t = string let compare = compare end)


module IntSet =
  Set.Make (struct type t = int let compare = compare end)


(* TODO this only works well with strings that have no newlines *)
let clipLeadingWhitespace s =
  if Str.string_match (Str.regexp "^[ ]*\\(.*\\)*$") s 0 then
    Str.matched_group 1 s
  else
    failwith "clipLeadingWhitespace"


let rec clip s =
  if s = "" then s
  else let (c,s') = (s.[0], String.sub s 1 (String.length s - 1)) in
       if c = ' '
         then clip s'
         else String.make 1 c ^ s'


(* may raise Not_found *)
let splitAround s c =
  let i = String.index s c in
  let i = succ i in
  (String.sub s 0 (i - 1), String.sub s i (String.length s - i))


let strAfterLast s c =
  try
    let i = String.rindex s c in
    let i = succ i in
    String.sub s i (String.length s - i)
  with Not_found ->
    s


let strPrefix s pre =
  let n = String.length s in
  let m = String.length pre in
    (n >= m) && (String.sub s 0 m = pre)


let strAfterPrefix s pre =
  if strPrefix s pre
  then let n = String.length pre in String.sub s n (String.length s - n)
  else failwith (Printf.sprintf "strAfterPrefix [%s] [%s]" s pre)


let iter_i f l =
  ignore (List.fold_left (fun i x -> f x i; succ i) 0 l)


let map_i f l =
  List.rev (snd
    (List.fold_left (fun (i,acc) x -> (succ i, (f x i)::acc)) (0,[]) l))


let fold_left_i f init l =
  snd (List.fold_left (fun (i,acc) x -> (succ i, f acc x i)) (0, init) l)


(* TODO factor the maybeFold pattern as a library func *)


let removeDupes l =
  List.fold_left (fun acc x -> if List.mem x acc then acc else x::acc) [] l


let someDupe l =
  let rec foo acc = function
    | []   -> None
    | h::t -> if List.mem h acc then Some(h) else foo (h::acc) t
  in foo [] l


let noDupes l = match someDupe l with Some _ -> false | None -> true


let list0N n =
  let rec foo acc i n =
    if i > n then acc
    else foo (i::acc) (succ i) n
  in
  List.rev (foo [] 0 n)


let list1N n = List.map succ (list0N (pred n))


let mapFst f l = List.map (fun (x, y) -> (f x, y)) l
let mapSnd f l = List.map (fun (x, y) -> (x, f y)) l


let take k l =
  let rec foo k acc l =
    if k = 0 then List.rev acc
    else match l with
      | h::t -> foo (pred k) (h::acc) t
      | []   -> failwith "take"
  in
  foo k [] l


let maybeAddToList l x = if List.mem x l then l else x :: l


let subtractList l1 l2 = (* subtract l2 from l1, maintain order of l1 *)
  List.rev
    (List.fold_left
      (fun acc x -> if List.mem x l2 then acc else x :: acc) [] l1)


let splitInMiddle l =
  if (List.length l) mod 2 = 1 then failwith "splitInMiddle: odd length";
  let rec foo acc i rest =
    if i = (List.length l) / 2 then (List.rev acc, rest)
    else foo (List.hd rest :: acc) (succ i) (List.tl rest)
  in
  foo [] 0 l


let longHeadShortTail = function
  | [] -> failwith "longHeadShortTail: need at least one element"
  | l  -> let lRev = List.rev l in
          (List.rev (List.tl lRev), List.hd lRev)


let safeCombine cap l1 l2 =
  if List.length l1 = List.length l2 then List.combine l1 l2
  else failwith (Printf.sprintf "safeCombine: called from [%s]" cap)


let stringMultiply s n sep =
  if n <= 0 then ""
  else String.concat sep (List.map (fun _ -> s) (list0N (pred n)))


let strStrList l = 
  Printf.sprintf "[%s]" (String.concat ", " l)


let strIntList l = 
  Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_int l))


module Counter =
  struct
    type t = int ref
    let create () = ref 0
    let next k = incr k; !k
    let count k = !k
    let clear k = k := 0
  end


let cartesianProduct lists =
  List.map List.rev
    (List.fold_left (fun tuples li ->
       List.fold_left (fun acc x ->
         let tuples' = List.map (fun l' -> x::l') tuples in
         acc @ tuples') [] li) [[]] lists)


let powerset items =
  let rec foo acc = function
    | []    -> acc
    | x::xs -> foo (acc @ List.map (fun l -> x::l) acc) xs
  in foo [[]] items


let powersetMaxSize n items =
  let rec foo acc = function
    | []    -> acc
    | x::xs -> foo (acc @ List.fold_left (fun acc' l ->
                            if List.length l < n then (x::l)::acc'
                            else acc') [] acc) xs
  in foo [[]] items


module IdTable =
  struct

    type 'a t = Counter.t * (int, 'a) Hashtbl.t * ('a, int) Hashtbl.t

    let create () = Counter.create (), Hashtbl.create 17, Hashtbl.create 17

    let process (k,t1,t2) x =
      if Hashtbl.mem t2 x then Hashtbl.find t2 x
      else
        let i = Counter.next k in
        Hashtbl.add t1 i x;
        Hashtbl.add t2 x i;
        i

    let mem (_,_,t2) = Hashtbl.mem t2

    let getId (_,_,t2) = Hashtbl.find t2

    let size (k,_,_) = Counter.count k

    let getVal (_,t1,_) = Hashtbl.find t1

    let clear (k,t1,t2) = Counter.clear k; Hashtbl.clear t1; Hashtbl.clear t2

    let iter f (_,t1,_) = Hashtbl.iter f t1

  end


let copyFile fFrom fTo =
  let (ic,oc) = (open_in fFrom, open_out fTo) in
  let rec foo () =
    try (Printf.fprintf oc "%s\n" (input_line ic); foo ())
    with End_of_file -> (close_in ic; close_out oc)
  in foo()


let timeThunk f =
  let timeBefore = Unix.gettimeofday () in
  let ret = f () in
  let timeDiff = Unix.gettimeofday () -. timeBefore in
  (timeDiff, ret)


(* TODO generalize *)
let redString s = Printf.sprintf "\027[31m%s\027[0m" s
let greenString s = Printf.sprintf "\027[32m%s\027[0m" s
let yellowString s = Printf.sprintf "\027[33m%s\027[0m" s

