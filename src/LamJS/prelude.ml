open Lexing

type id = string

(** We track the start and end position of each syntactic form. *)
type pos = Lexing.position * Lexing.position 

module IdOrderedType = struct
  type t = id
  let compare = Pervasives.compare
end

module Pos = struct

  type t = pos

  let compare = Pervasives.compare

  let before (_, p1_end) (p2_start, _) = 
    p1_end.pos_cnum < p2_start.pos_cnum
end

module Int = struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make (Int)
module IntSetExt = SetExt.Make (IntSet)

module IdSet = Set.Make (IdOrderedType)

module IdSetExt = SetExt.Make (IdSet)

module PosSet = Set.Make (Pos)

module PosSetExt = SetExt.Make (PosSet)

module PosMap = Map.Make (Pos)

module PosMapExt = MapExt.Make (Pos) (PosMap)

module IdMap = Map.Make (IdOrderedType)

module IdMapExt = MapExt.Make (IdOrderedType) (IdMap)

let fold_left = List.fold_left

let fold_right = List.fold_right

let map = List.map

let printf = Printf.printf

let eprintf = Printf.eprintf

let sprintf = Printf.sprintf

let second2 f (a, b) = (a, f b)

let third3 f (a, b, c) = (a, b, f c)

let string_of_position (p, e) = 
  Format.sprintf "%s:%d:%d-%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
    (e.pos_cnum - e.pos_bol)

let snd3 (a, b, c) = b

let snd2 (a, b) = b

let fst2 (a, b) = a

let fst3 (a, _, _) = a

let thd3 (_, _, c) = c

let rec intersperse a lst = match lst with
    [] -> []
  | [x] -> [x]
  | x :: xs -> x :: a :: (intersperse a xs)

let rec take_while f xs = match xs with
    [] -> [], []
  | x :: xs' -> 
      if f x then
        let lhs, rhs = take_while f xs' in
          x :: lhs, rhs
      else
        [], xs

let rec match_while f xs = match xs with
    [] -> [], []
  | x :: xs' -> begin match f x with
        Some y ->
          let ys, xs'' = match_while f xs' in
            y :: ys, xs''
      | None -> [], xs
    end



let rec rem (elt : 'a) (lst : 'a list) : 'a list = match lst with
    [] -> []
  | x :: xs -> if elt = x then rem elt xs else x :: (rem elt xs)

let rec nub (lst : 'a list) : 'a list = match lst with
    [] -> []
  | x :: xs -> x :: (nub (rem x xs))

let rec iota' m lst = 
  if m < 0 then lst
  else iota' (m - 1) (m :: lst)

let iota n = iota' (n - 1) []
