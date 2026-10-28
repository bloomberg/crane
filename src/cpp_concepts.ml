(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ concept a module type becomes ({!Modtype_concept.t}), as text:
    its declaration, the concepts of the module types nested in it, and the
    name every reference to it spells. *)

open Pp
open Util
open Names
open Common
open Minicpp
open Cpp_state
open Cpp_names
open Cpp_print

(** Render a custom type mapping (e.g. ["std::pair<%t0,%t1>"]) with each of
    its type holes qualified by [qualify_type].

    This is what lets a parametric custom type appear in a module signature's
    [requires] clause: the arguments spliced into it need the same
    ["typename M::"] qualification the surrounding concept gives everything
    else.  A hole with no corresponding argument is left as written.

    @param custom_str  The mapping as the user wrote it.
    @param args        The C++ type arguments filling [%t0], [%t1], ….
    @param qualify_type  Renders one argument, qualified. *)
let qualify_custom_template custom_str args qualify_type =
  render_type_template custom_str
    ~hole:(fun i -> Option.map qualify_type (List.nth_opt args i))

(** What a module type contributes where a concept body is expected.

    [MTident] and its refinements name a concept that already exists; only an
    anonymous signature has requirements of its own, and those are a list of
    lines rather than one blob, so "does this concept ask for anything" is a
    question about the list and not about the rendered text. *)
type module_constraint = MCname of Pp.t | MCrequirements of Pp.t list

(** A module type's contribution as one document. *)
let module_constraint_pp = function
  | MCname n -> n
  | MCrequirements reqs -> prlist identity reqs

(** The body of a [concept N = ...] declaration for a module type, or [None]
    when the module type asks for nothing and the concept is just [true]. *)
let concept_body_pp = function
  | MCrequirements [] -> None
  | mc -> Some (module_constraint_pp mc)

(** [concept N = requires { ... };], or [concept N = true;] when the module
    type asks for nothing.  The one spelling of a module type's concept, minus
    the [template<typename M>] line that introduces it. *)
let pp_concept_clause name = function
  | None -> (str "concept " ++ name ++ str " = true;")
  | Some body ->
    ( str "concept "
      ++ name
      ++ str " = requires {"
      ++ fnl ()
      ++ body
      ++ str "};" )

(** {!pp_concept_clause} with its [template<typename M>] introduction. *)
let pp_concept_def name body =
  str "template<typename M>" ++ fnl () ++ pp_concept_clause name body

(** The type member [name] of [M], an enum's capitalised, applied to [args]
    when it is a template. *)
let pp_member_type ~enum name r args =
  let name = Cpp_name.pp (if enum then enum_name name r else name) in
  let m = Cpp_name.pp_scope (Cpp_name.Parameter "M") in
  match args with
  | [] -> str "typename " ++ m ++ name
  | _ ->
    str "typename " ++ m ++ str "template " ++ name ++ str "<"
    ++ prlist_with_sep (fun () -> str ", ") Fun.id args
    ++ str ">"

(* What printing a module type's concept names, at the frames it names them
   in: {!pp_modtype_concept}, read without printing it.  The type printer
   names the globals of the types it writes ({!Cpp_print.global_names}). *)

let type_names frame ty = global_names [frame] (Cpp_demands.globals_of_type ty)

let rec concept_type_names frame : Modtype_concept.concept_type -> _ = function
  | Member {member; arguments; _} -> (frame, Cpp_resolution.Global (Type, member)) :: concept_types_names frame arguments
  | Global (r, args) -> type_names frame (Tglob (r, [], [])) @ concept_types_names frame args
  | Namespaced (r, r', e, args) -> type_names frame (Tnamespace (r, Tglob (r', [], e))) @ concept_types_names frame args
  | Foreign (_, args) | Variant (_, args) -> concept_types_names frame args
  | Shared_pointer ty -> concept_type_names frame ty
  | Function (dom, cod) -> concept_types_names frame (cod :: dom)
  | Parameter ty | Plain ty -> type_names frame ty

and concept_types_names frame tys = List.concat_map (concept_type_names frame) tys

let requirement_names frame : Modtype_concept.requirement -> _ = function
  | Inductive_member {member; _} -> [(frame, Cpp_resolution.Short (Type, member))]
  | Type_member {member; _} -> [(frame, Unmapped (Type, member))]
  | Instance_member {value; class_; arguments} ->
    (frame, Cpp_resolution.Unmapped (Term, value)) :: (frame, Short (Type, class_)) :: concept_types_names frame arguments
  | Nullary_member {value; result} -> (frame, Cpp_resolution.Unmapped (Term, value)) :: concept_type_names frame result
  | Function_member {value; parameters; result} ->
    (frame, Cpp_resolution.Unmapped (Term, value)) :: concept_types_names frame (result :: parameters)
  | Submodule {module_type; _} -> [(frame, Modtype_concept module_type)]

let rec constraint_names frame : Modtype_concept.constraint_ -> _ = function
  | Named kn -> [(frame, Cpp_resolution.Module kn)]
  | Requirements {signature; parameters; items} ->
    let frame = Cpp_resolution.Signature {signature; parameters} :: frame in
    List.concat_map
      (function
        | Modtype_concept.Requirement r -> requirement_names frame r
        | Nested (path, c) -> (frame, Cpp_resolution.Modtype_concept_declared path) :: constraint_names frame c )
      items

let modtype_concept_names ~path ~params (c : Modtype_concept.t) =
  let modules frame = List.map (fun p -> (frame, Cpp_resolution.Module p)) in
  (([], Cpp_resolution.Modtype_concept_declared path) :: modules [] params)
  @
  match c with
  | Alias {base; refinements} ->
    (([], Cpp_resolution.Modtype_concept base) :: modules [] (concept_extra_args base))
    @ List.concat_map (fun (_, ty) -> type_names [] ty) refinements
  | Constraint c -> constraint_names [] c

(** A type of a module-type concept's requirements, spelled from inside the
    concept ({!Modtype_concept.concept_type}), naming what [names] names at
    [frame]. *)
let rec pp_concept_type names frame (t : Modtype_concept.concept_type) : Pp.t =
  let pp_concept_type = pp_concept_type names frame in
  match t with
  | Member {member; enum; arguments} ->
    pp_member_type ~enum (name_in names frame (Global (Type, member))) member (List.map pp_concept_type arguments)
  | Parameter ty -> str "typename " ++ pp_cpp_type false [] ty
  | Foreign (template, args) -> qualify_custom_template template args pp_concept_type
  | Global (r, []) -> pp_cpp_type false [] (Tglob (r, [], []))
  | Global (r, args) ->
    pp_cpp_type false [] (Tglob (r, [], []))
    ++ str "<"
    ++ prlist_with_sep (fun () -> str ", ") pp_concept_type args
    ++ str ">"
  | Namespaced (r, r', e, []) -> pp_cpp_type false [] (Tnamespace (r, Tglob (r', [], e)))
  | Namespaced (r, r', e, args) ->
    pp_cpp_type false [] (Tnamespace (r, Tglob (r', [], e)))
    ++ str "<"
    ++ prlist_with_sep (fun () -> str ", ") pp_concept_type args
    ++ str ">"
  | Shared_pointer ty -> str ((sn ()).ns ^ "::") ++ str "shared_ptr<" ++ pp_concept_type ty ++ str ">"
  | Variant (Inline_variant, tys) ->
    str ((sn ()).ns ^ "::")
    ++ str "variant<"
    ++ prlist_with_sep (fun () -> str ", ") pp_concept_type tys
    ++ str ">"
  | Variant (Shared_variant, tys) ->
    str Crane_rt.shared_variant
    ++ str "<"
    ++ prlist_with_sep (fun () -> str ", ") pp_concept_type tys
    ++ str ">"
  | Function (dom, cod) ->
    writes (Table.Runtime Crane_rt.fn_header);
    str Crane_rt.fn ++ str "<"
    ++ pp_concept_type cod
    ++ str "("
    ++ prlist_with_sep (fun () -> str ", ") pp_concept_type dom
    ++ str ")>"
  | Plain ty -> pp_cpp_type false [] ty

(** One line of a module-type concept's [requires] clause
    ({!Modtype_concept.requirement}).  A nullary value may be a static data
    member or, inside a template where it becomes a Meyers singleton, a
    nullary accessor; which one a functor body uses is decided by
    per-reference resolution later, so both are accepted. *)
let pp_requirement names frame : Modtype_concept.requirement -> Pp.t =
  let name key = name_in names frame key in
  let pp_concept_type = pp_concept_type names frame in
  function
  | Inductive_member {member; enum; arity} ->
    let placeholders = List.init arity (fun _ -> pp_cpp_type false [] Tany) in
    pp_member_type ~enum (name (Short (Type, member))) member placeholders ++ str ";" ++ fnl ()
  | Type_member {member; arity} ->
    let name = Cpp_name.pp (name (Unmapped (Type, member))) in
    if arity = 0 then str "typename M::" ++ name ++ str ";" ++ fnl ()
    else
      str "typename M::template "
      ++ name
      ++ str "<"
      ++ prlist_with_sep (fun () -> str ", ") identity (List.init arity (fun _ -> str "void"))
      ++ str ">;"
      ++ fnl ()
  | Instance_member {value; class_; arguments} ->
    let value = Cpp_name.pp (name (Unmapped (Term, value))) in
    writes_standard "concepts";
    str "typename M::"
    ++ value
    ++ str ";"
    ++ fnl ()
    ++ str "requires "
    ++ str (Cpp_name.to_string (name (Short (Type, class_))))
    ++ str "<typename M::"
    ++ value
    ++ prlist (fun a -> str ", " ++ pp_concept_type a) arguments
    ++ str ">;"
    ++ fnl ()
  | Nullary_member {value; result} ->
    let name = Cpp_name.pp (name (Unmapped (Term, value))) in
    let convertible_to = (sn ()).convertible_to in
    writes_standard "concepts";
    let qualified_ret = pp_concept_type result in
    str "requires ("
    ++ fnl ()
    ++ str "  requires { { M::"
    ++ name
    ++ str " } -> "
    ++ str convertible_to
    ++ str "<"
    ++ qualified_ret
    ++ str ">; } ||"
    ++ fnl ()
    ++ str "  requires { { M::"
    ++ name
    ++ str "() } -> "
    ++ str convertible_to
    ++ str "<"
    ++ qualified_ret
    ++ str ">; }"
    ++ fnl ()
    ++ str ");"
    ++ fnl ()
  | Function_member {value; parameters; result} ->
    let name = Cpp_name.pp (name (Unmapped (Term, value))) in
    let same_as = (sn ()).same_as in
    let declval = (sn ()).declval in
    writes_standard "concepts";
    let declvals =
      List.map (fun ty -> str declval ++ str "<" ++ pp_concept_type ty ++ str ">()") parameters
    in
    let call_expr =
      str "M::" ++ name ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity declvals ++ str ")"
    in
    str "{ "
    ++ call_expr
    ++ str " } -> "
    ++ str same_as
    ++ str "<"
    ++ pp_concept_type result
    ++ str ">;"
    ++ fnl ()
  | Submodule {label; module_type} ->
    str "  requires "
    ++ Cpp_name.pp (name (Modtype_concept module_type))
    ++ str "<typename M::"
    ++ str (Label.to_string label)
    ++ str ">;"
    ++ fnl ()

(** What a module type contributes where a concept body is expected
    ({!Modtype_concept.constraint_}), with the concepts of the module types
    nested in it, which are declared ahead of the concept it is the body of,
    innermost first.  An anonymous signature's requirements are printed with
    the signature and the functor parameters visible in it visible, which
    is the frame [names] names them at. *)
let rec pp_constraint names frame : Modtype_concept.constraint_ -> Pp.t list * module_constraint = function
  | Named kn -> ([], MCname (Cpp_name.pp (name_in names frame (Module kn))))
  | Requirements {signature; parameters; items} ->
    let entered = Cpp_resolution.Signature {signature; parameters} in
    let frame = entered :: frame in
    enter entered @@ fun () ->
    let item (hoisted, reqs) : Modtype_concept.item -> _ = function
      | Requirement req -> (hoisted, pp_requirement names frame req :: reqs)
      | Nested (path, c) ->
        let inner, nested = pp_constraint names frame c in
        let def = pp_concept_def (Cpp_name.pp (name_in names frame (Modtype_concept_declared path))) (concept_body_pp nested) in
        (def :: List.rev_append inner hoisted, reqs)
    in
    let hoisted, reqs = List.fold_left item ([], []) items in
    (List.rev hoisted, MCrequirements (List.rev reqs))

(** The [std::same_as] constraints the [with Definition] refinements of a
    module type conjoin onto the concept it refines
    ({!Modtype_concept.Alias}): [BASE with Definition t := nat] asks for
    [std::same_as<typename M::t, uint64_t>] on top of [BASE]'s concept. *)
let pp_refinements refinements =
  let clauses =
    List.map
      (fun (idl, cpp) ->
        let path = String.concat "::" (List.map Id.to_string idl) in
        str (sn ()).same_as
        ++ str "<typename M::"
        ++ str path
        ++ str ", "
        ++ pp_cpp_type false [] cpp
        ++ str ">" )
      refinements
  in
  if clauses <> [] then writes_standard "concepts";
  clauses

(** The declaration of the concept of the module type at [path], generated
    as [c], with the concepts its nested module types are hoisted into ahead
    of it, naming what [names] names.  The concept is over [M], the module
    it constrains, and over [params], the parameters of a functor declaring
    it, which its requirements may mention. *)
let pp_modtype_concept ~names ~params path (c : Modtype_concept.t) =
  let here key = Cpp_name.pp (name_in names [] key) in
  let name = here (Modtype_concept_declared path) in
  let head =
    str "template<typename M"
    ++ prlist (fun p -> str ", typename " ++ here (Module p)) params
    ++ str ">" ++ fnl ()
  in
  match c with
  | Alias {base; refinements} ->
    let base_args =
      prlist (fun p -> str ", " ++ here (Module p)) (concept_extra_args base)
    in
    head ++ str "concept " ++ name ++ str " = " ++ here (Modtype_concept base)
    ++ str "<M" ++ base_args ++ str ">"
    ++ prlist (fun c -> str " && " ++ c) (pp_refinements refinements)
    ++ str ";"
  | Constraint c ->
    let hoisted, body = pp_constraint names [] c in
    prlist_with_sep (fun () -> fnl () ++ fnl ()) identity
      (hoisted @ [head ++ pp_concept_clause name (concept_body_pp body)])

(** The one spelling of "this subject satisfies this concept", on a line of
    its own. *)
let pp_assertion (a : Cpp_ast.assertion) =
  let concept =
    match a.concept with
    | Of_module_type c -> Cpp_name.pp (resolved_concept c)
    | Of_class c -> Cpp_name.pp (resolved_class_concept c)
  in
  let subject =
    match a.subject with
    | Module m -> module_struct_name_of (resolved_module m)
    | Instance {instance; args} ->
      Cpp_name.pp (resolved_type_name instance) ++ prlist (fun ty -> str ", " ++ pp_cpp_type false [] ty) args
  in
  fnl () ++ str "static_assert(" ++ concept ++ str "<" ++ subject ++ str ">);"

let names_requested : Cpp_ast.declaration -> _ = function
  | Modtype_concept {path; params; concept; _} -> modtype_concept_names ~path ~params concept
  | Declaration _ | Absorbed _ | Fields _ | Global_alias _ | Assertion _ | Module_alias _ | Functor_alias _
  | Derived_functor _ ->
    []
