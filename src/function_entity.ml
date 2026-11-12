(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A finished declaration split into its declaration and definition.  See
    [function_entity.mli]. *)

open Cpp_ir

type t = {
  declaration : Cpp_erasure.settled;
  definition : Cpp_erasure.settled;
  declaration_ir : Resolved.Decl.t;
  definition_ir : Resolved.Decl.t;
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

(* Under [CRANE_CHECK_IR], splitting the CppIR declaration [ir] gives what
   splitting its MiniCpp twin [d] and converting the halves does. *)
let check_split d ir =
  let converted (d : Cpp_erasure.settled) =
    match Legacy_minicpp_to_cpp_ir.convert d with
    | Ok d -> Some d
    | Error _ -> None
  in
  let twin = Option.map (fun (a, b) -> (converted a, converted b)) (Cpp_erasure.split_definition d) in
  let split = Option.map (fun (a, b) -> (Some a, Some b)) (split_definition ir) in
  let stripped = converted (Cpp_erasure.strip_template_defaults d) in
  if compare twin split <> 0 || compare stripped (Some (strip_template_defaults ir)) <> 0 then
    Probe.violation "CppIR function entity" (Pp.str "a definition splits differently in CppIR")

let of_finished d ir =
  if Probe.checking () then check_split d ir;
  match (Cpp_erasure.split_definition d, split_definition ir) with
  | Some (declaration, definition), Some (declaration_ir, definition_ir) ->
    {declaration; definition; declaration_ir; definition_ir; defines_function = true}
  | None, None -> {declaration = d; definition = d; declaration_ir = ir; definition_ir = ir; defines_function = false}
  | Some _, None | None, Some _ -> CErrors.anomaly (Pp.str "Crane: a definition splits in one IR only.")

let declaration e = e.declaration
let definition e = e.definition
let definition_after_declaration e = Cpp_erasure.strip_template_defaults e.definition
let declaration_ir e = e.declaration_ir
let definition_ir e = e.definition_ir
let definition_after_declaration_ir e = strip_template_defaults e.definition_ir
let defines_function e = e.defines_function
