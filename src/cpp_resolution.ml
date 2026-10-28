(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type entered =
  | Signature of {signature : ModPath.t; parameters : ModPath.t list}
  | Inductive_struct of GlobRef.t
  | In_struct
  | In_template
  | Function of {owner : GlobRef.t; defines : bool}
type frame = entered list
type definition = Enum_definition | Struct_definition | Alias_definition

type key =
  | Module of ModPath.t
  | Module_declared of ModPath.t
  | Global of Common.kind * GlobRef.t
  | Unmapped of Common.kind * GlobRef.t
  | Inductive_value of GlobRef.t
  | Short of Common.kind * GlobRef.t
  | Class_concept of GlobRef.t
  | Modtype_concept of ModPath.t
  | Modtype_concept_declared of ModPath.t
  | Definition of definition * GlobRef.t

let pp_key k =
  let global what r = Pp.(str what ++ str " " ++ GlobRef.print r) in
  let path what mp = Pp.str (what ^ " " ^ ModPath.to_string mp) in
  match k with
  | Module mp -> path "the module" mp
  | Module_declared mp -> path "the declared name of the module" mp
  | Global (_, r) -> global "the global" r
  | Unmapped (_, r) -> global "the unmapped global" r
  | Inductive_value r -> global "the value of the inductive" r
  | Short (_, r) -> global "the short name of" r
  | Class_concept r -> global "the concept of" r
  | Modtype_concept mp -> path "the concept of the module type" mp
  | Modtype_concept_declared mp -> path "the declared concept of the module type" mp
  | Definition (_, r) -> global "the definition of" r

let compare_entered a b =
  let rank = function Signature _ -> 0 | Inductive_struct _ -> 1 | In_struct -> 2 | In_template -> 3 | Function _ -> 4 in
  match (a, b) with
  | Signature a, Signature b -> (
    match ModPath.compare a.signature b.signature with
    | 0 -> List.compare ModPath.compare a.parameters b.parameters
    | c -> c )
  | Inductive_struct a, Inductive_struct b -> GlobRef.UserOrd.compare a b
  | Function a, Function b -> (
    match GlobRef.UserOrd.compare a.owner b.owner with 0 -> Bool.compare a.defines b.defines | c -> c )
  | _ -> Int.compare (rank a) (rank b)

let compare_kind (a : Common.kind) b = compare a b

let compare_key a b =
  let rank = function
    | Module _ -> 0
    | Module_declared _ -> 1
    | Global _ -> 2
    | Unmapped _ -> 3
    | Inductive_value _ -> 4
    | Short _ -> 5
    | Class_concept _ -> 6
    | Modtype_concept _ -> 7
    | Modtype_concept_declared _ -> 8
    | Definition _ -> 9
  in
  let global ka ra kb rb = match compare_kind ka kb with 0 -> GlobRef.UserOrd.compare ra rb | c -> c in
  match (a, b) with
  | Module a, Module b
  | Module_declared a, Module_declared b
  | Modtype_concept a, Modtype_concept b
  | Modtype_concept_declared a, Modtype_concept_declared b ->
    ModPath.compare a b
  | Global (ka, ra), Global (kb, rb) | Unmapped (ka, ra), Unmapped (kb, rb) | Short (ka, ra), Short (kb, rb) ->
    global ka ra kb rb
  | Class_concept a, Class_concept b | Inductive_value a, Inductive_value b -> GlobRef.UserOrd.compare a b
  | Definition (da, a), Definition (db, b) -> ( match compare da db with 0 -> GlobRef.UserOrd.compare a b | c -> c )
  | _ -> Int.compare (rank a) (rank b)

module Map = Map.Make (struct
  type t = frame * key

  let compare (fa, ka) (fb, kb) = match List.compare compare_entered fa fb with 0 -> compare_key ka kb | c -> c
end)

type table = Unresolved_table | Resolved of Cpp_name.t Map.t

let unresolved = Unresolved_table

let resolve name requests =
  Resolved
    (List.fold_left
       (fun m ((frame, key) as k) -> if Map.mem k m then m else Map.add k (name frame key) m)
       Map.empty requests )

type lookup = Found of Cpp_name.t | Unresolved | Not_requested

let find t frame key =
  match t with
  | Unresolved_table -> Unresolved
  | Resolved m -> ( match Map.find_opt (frame, key) m with Some n -> Found n | None -> Not_requested )
