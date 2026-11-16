(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a unit's declarations sit in structs.  See [struct_plan.mli]. *)

open Names

type accessors = {
  accessor_names : (ModPath.t * Label.t) list;
  accessor_constants : KerName.t list;
}

let no_accessors = {accessor_names = []; accessor_constants = []}

let add_accessor a mp lbl =
  let known (mp', lbl') = ModPath.equal mp mp' && Label.equal lbl lbl' in
  if List.exists known a.accessor_names then a else {a with accessor_names = (mp, lbl) :: a.accessor_names}

let add_accessor_ref a r =
  let a = add_accessor a (Base.Table.modpath_of_r r) (Base.Table.label_of_r r) in
  match r with
  | GlobRef.ConstRef c ->
    let kn = Constant.canonical c in
    if List.mem kn a.accessor_constants then a else {a with accessor_constants = kn :: a.accessor_constants}
  | _ -> a

let is_accessor_constant a c = List.mem (Constant.canonical c) a.accessor_constants

let is_accessor a mp lbl =
  List.exists (fun (mp', lbl') -> ModPath.equal mp mp' && Label.equal lbl lbl') a.accessor_names

type nested_struct_owner = Global of GlobRef.t | Module of ModPath.t

type nested_structs = nested_struct_owner list CString.Map.t

let nested_struct_owner_equal a b =
  match (a, b) with
  | Global x, Global y -> Base.Common.globref_equal x y
  | Module x, Module y -> ModPath.equal x y
  | _ -> false

let nested_struct_owner_covers r = function
  | Global r' -> Base.Common.globref_equal r r'
  | Module mp -> ModPath.equal mp (Base.Table.modpath_of_r r)

let add_nested_struct_name m (name, owner) =
  let prev = Option.default [] (CString.Map.find_opt name m) in
  if List.exists (nested_struct_owner_equal owner) prev then m else CString.Map.add name (owner :: prev) m
