(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The pointer fields of constructor structs.  See [pointer_fields.mli]. *)

type field = Recursive of int | Boxed of int

let index = function Recursive i | Boxed i -> i

module Key = struct
  type t = string * string

  let compare (o, c) (o', c') = match String.compare o o' with 0 -> String.compare c c' | n -> n
end

module Map = Map.Make (Key)

type planned = {
  index : int;
  recursive : bool;
  in_slot : bool;
}

type t = planned list Map.t

let none = Map.empty

let add m planned =
  List.fold_left
    (fun m (owner, ctor_name, fields) -> Map.add (Base.Common.ctor_owner_key owner, ctor_name) fields m)
    m planned

let find m key =
  Option.map (List.map (fun p -> if p.recursive then Recursive p.index else Boxed p.index)) (Map.find_opt key m)

let cells m key =
  Option.map (List.filter_map (fun p -> if p.in_slot then None else Some p.index)) (Map.find_opt key m)
