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
type enumerator_site = Enumerator_value | Case_label
type head_form = Glob_head | Inductive_head

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
  | Custom_text of GlobRef.t
  | Inline_custom of GlobRef.t
  | Inductive_scope of GlobRef.t
  | Type_head of head_form * GlobRef.t
  | Value_reference of GlobRef.t
  | Value_access of GlobRef.t
  | Built_struct of GlobRef.t
  | Enumerator_qualifier of enumerator_site * GlobRef.t
  | Read_by_a_function of GlobRef.t
  | Held_back_concept of GlobRef.t

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
  | Custom_text r -> global "the custom text of" r
  | Inline_custom r -> global "the inline custom text of" r
  | Inductive_scope r -> global "the struct naming the members of" r
  | Type_head (Glob_head, r) -> global "the type head of" r
  | Type_head (Inductive_head, r) -> global "the inductive type head of" r
  | Value_reference r -> global "the value reference to" r
  | Value_access r -> global "how a value reads" r
  | Built_struct r -> global "the struct a value is built through of" r
  | Enumerator_qualifier (Enumerator_value, r) -> global "the enum an enumerator value names of" r
  | Enumerator_qualifier (Case_label, r) -> global "the enum a case label names of" r
  | Read_by_a_function r -> global "whether a function reads" r
  | Held_back_concept r -> global "whether the concept is held back of" r

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
    | Custom_text _ -> 10
    | Inline_custom _ -> 11
    | Inductive_scope _ -> 12
    | Type_head _ -> 13
    | Value_reference _ -> 14
    | Value_access _ -> 15
    | Built_struct _ -> 16
    | Enumerator_qualifier _ -> 17
    | Read_by_a_function _ -> 18
    | Held_back_concept _ -> 19
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
  | Class_concept a, Class_concept b
  | Inductive_value a, Inductive_value b
  | Custom_text a, Custom_text b
  | Inline_custom a, Inline_custom b
  | Inductive_scope a, Inductive_scope b
  | Value_reference a, Value_reference b
  | Value_access a, Value_access b
  | Built_struct a, Built_struct b
  | Read_by_a_function a, Read_by_a_function b
  | Held_back_concept a, Held_back_concept b ->
    GlobRef.UserOrd.compare a b
  | Enumerator_qualifier (sa, a), Enumerator_qualifier (sb, b) -> (
    match compare sa sb with 0 -> GlobRef.UserOrd.compare a b | c -> c )
  | Type_head (fa, a), Type_head (fb, b) -> ( match compare fa fb with 0 -> GlobRef.UserOrd.compare a b | c -> c )
  | Definition (da, a), Definition (db, b) -> ( match compare da db with 0 -> GlobRef.UserOrd.compare a b | c -> c )
  | _ -> Int.compare (rank a) (rank b)

module Map = Map.Make (struct
  type t = frame * key

  let compare (fa, ka) (fb, kb) = match List.compare compare_entered fa fb with 0 -> compare_key ka kb | c -> c
end)

type head = {outer : Cpp_name.scope list; head : Cpp_name.t; typename : bool; templated : bool}
type reference =
  | Named_value of {name : Cpp_name.t; type_arguments : bool}
  | Record_member of {record : GlobRef.t; type_params : int}

type access = Variable | Accessor | Either_form

type value =
  | Name of Cpp_name.t
  | Head of head
  | Inline of string option
  | Reference of reference
  | Access of access
  | Holds of bool

let pp_reference = function
  | Named_value {name; type_arguments} ->
    Pp.(str (Cpp_name.to_string name) ++ if type_arguments then str " with its type arguments" else mt ())
  | Record_member {record; type_params} ->
    Pp.(str "a member of " ++ GlobRef.print record ++ str " of " ++ int type_params ++ str " parameters")

let pp_access = function
  | Variable -> Pp.str "a variable"
  | Accessor -> Pp.str "an accessor"
  | Either_form -> Pp.str "a variable or an accessor"

let not_a key what = CErrors.anomaly Pp.(str "Crane: " ++ pp_key key ++ str " did not resolve to " ++ str what ++ str ".")

let name_of key = function
  | Name n -> n
  | Head _ -> CErrors.anomaly Pp.(str "Crane: " ++ pp_key key ++ str " is a type's head, not a name.")
  | Inline _ -> CErrors.anomaly Pp.(str "Crane: " ++ pp_key key ++ str " is an inline custom answer, not a name.")
  | Reference _ | Access _ | Holds _ -> not_a key "a name"

let head_of key = function Head h -> h | _ -> not_a key "a type's head"
let inline_of key = function Inline text -> text | _ -> not_a key "an inline custom answer"
let reference_of key = function Reference r -> r | _ -> not_a key "a value reference"
let access_of key = function Access a -> a | _ -> not_a key "an access"
let holds_of key = function Holds b -> b | _ -> not_a key "whether it holds"

type table = Unresolved_table | Resolved of value Map.t

let unresolved = Unresolved_table

let resolve value requests =
  Resolved
    (List.fold_left
       (fun m ((frame, key) as k) -> if Map.mem k m then m else Map.add k (value frame key) m)
       Map.empty requests )

type 'a lookup = Found of 'a | Unresolved | Not_requested

let lookup read t frame key =
  match t with
  | Unresolved_table -> Unresolved
  | Resolved m -> ( match Map.find_opt (frame, key) m with Some v -> Found (read key v) | None -> Not_requested )

let find t frame key = lookup name_of t frame key
let find_head t frame form r = lookup head_of t frame (Type_head (form, r))
let find_inline t frame r = lookup inline_of t frame (Inline_custom r)
let find_reference t frame r = lookup reference_of t frame (Value_reference r)
let find_access t frame r = lookup access_of t frame (Value_access r)
let find_holds t frame key = lookup holds_of t frame key
