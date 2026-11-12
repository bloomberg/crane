(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A finished declaration split into its declaration and definition.  See
    [function_entity.mli]. *)

open Cpp_ir

type t = {
  declaration : Resolved.Decl.t;
  definition : Resolved.Decl.t;
  defines_function : bool;
}

(* A function's definition, and its declaration naming every parameter its
   definition names. *)
let rec split_definition : Resolved.Decl.t -> (Resolved.Decl.t * Resolved.Decl.t) option = function
  | Function ({shape = Definition (params, _); _} as f) ->
    Some (Function {f with shape = Declaration (List.map (fun (x, t) -> (Some x, t)) params)}, Function f)
  | Template (params, constraint_, inner) ->
    Option.map
      (fun (decl, def) -> (Decl.Template (params, constraint_, decl), Decl.Template (params, constraint_, def)))
      (split_definition inner)
  | _ -> None

(* [d] with no template parameter's default. *)
let rec strip_template_defaults : Resolved.Decl.t -> Resolved.Decl.t = function
  | Template (params, constraint_, inner) ->
    let plain ((k : _ Template.Parameter_kind.t), x) =
      match k with Typename_default _ -> (Template.Parameter_kind.Typename, x) | _ -> (k, x)
    in
    Template (List.map plain params, constraint_, strip_template_defaults inner)
  | d -> d

let of_finished d =
  match split_definition d with
  | Some (declaration, definition) -> {declaration; definition; defines_function = true}
  | None -> {declaration = d; definition = d; defines_function = false}

let declaration e = e.declaration
let definition e = e.definition
let definition_after_declaration e = strip_template_defaults e.definition
let defines_function e = e.defines_function
