open Format
open FormatExt

module type S = sig
  type elt
  type t

  val unions : t list -> t
  val from_list : elt list -> t
  val to_list : t -> elt list
  val p_set : (elt -> printer) -> t -> printer
end

module Make (Set : Set.S) = struct
  
  type elt = Set.elt

  type t = Set.t

  let unions lst = List.fold_left Set.union Set.empty lst

  let from_list lst = 
    List.fold_left (fun set x -> Set.add x set) Set.empty lst

  let to_list set =
    Set.fold (fun e lst -> e :: lst) set []    

  let p_set p_elt set = 
    braces (horz (List.map p_elt (to_list set)))

end
