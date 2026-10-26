(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ concept a module type becomes ({!Modtype_concept.t}), as text:
    its declaration, the concepts of the module types nested in it, and the
    name every reference to it spells. *)

open Pp
open Util
open Names
open ModPath
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

(** The functor whose body declares module types at [mp], as
    {!Cpp_state.functor_concept_scopes} records it. *)
let functor_concept_scope mp =
  List.find_map
    (fun (m, scope) -> if ModPath.equal m mp then Some scope else None)
    !functor_concept_scopes

(** The arguments, after the constrained module, of the concept of the module
    type [kn]: the parameters of the functor declaring it, if one does. *)
let concept_extra_args kn =
  match kn with
  | MPdot (mp0, _) -> (
    match functor_concept_scope mp0 with Some (_, params) -> params | None -> [] )
  | _ -> []

(** The C++ identifier of the concept the module type at [mp] becomes, at
    its declaration and at every reference: named after the functor whose
    body declares it, where one does ({!functor_concept_scope}); qualified
    with its module where another concept shares its name
    ({!Module_plan.modtype_concept_name}); and otherwise its label
    ({!Structure_analysis.concept_name_of_label}).  Every site naming a
    module-type concept goes through this, so no two can disagree. *)
let modtype_concept_name mp =
  let base = Structure_analysis.concept_name_of_label in
  match mp with
  | MPdot (mp0, l) -> (
    match functor_concept_scope mp0 with
    | Some (fl, _) -> base fl ^ "_" ^ base l
    | None -> Option.default (base l) (Module_plan.modtype_concept_name mp) )
  | MPfile _ | MPbound _ ->
    CErrors.anomaly (Pp.str "modtype_concept_name: a module type is a member of a structure")

(** Render a concept name from a module path reference.  In separate extraction,
    concepts live inside their own namespace, so cross-file references need
    qualification.  For a top-level module type [X] that is its own extraction
    unit, the C++ structure is [namespace X { concept X = ...; }], requiring
    [X::X] from outside. *)
let pp_concept_ref kn =
  match kn with
  | MPdot (mp0, _) when Option.has_some (functor_concept_scope mp0) ->
    (* Declared at file scope, so named after the functor declaring it. *)
    str (modtype_concept_name kn)
  | MPdot (mp0, l') ->
    if get_force_cross_file_qualification () then begin
      (* Separate extraction: pp_modname produces visibility-aware names. *)
      let resolved = Common.resolve_module kn in
      let name = str (Common.resolved_string resolved) in
      (* Self-qualify when the concept is a top-level module type from a
         different file: its namespace and concept share a name, so from
         outside [ConceptName] refers to the namespace — we need
         [ConceptName::ConceptName].

         The file is the one holding the module whose element is being
         written, which the plan says, not the visibility in effect. *)
      let rec get_file_mp = function
        | ModPath.MPfile _ as mp -> mp
        | ModPath.MPdot (mp, _) -> get_file_mp mp
        | ModPath.MPbound _ -> mp0  (* functor param scope — treat as same *)
      in
      let current_file_mp = get_file_mp (module_written ()) in
      if (match mp0 with MPfile _ -> true | _ -> false)
         && not (ModPath.equal mp0 current_file_mp)
         && not (Common.resolved_is_qualified resolved) then
        name ++ str "::" ++ str (modtype_concept_name kn)
      else
        name
    end else begin
      (* Monolithic extraction: pp_module may over-qualify same-module
         concepts because the visibility context shifts inside
         pp_module_type.  Keep the short label and just trigger include
         tracking. *)
      ignore (Common.pp_module kn);
      str (modtype_concept_name kn)
    end
  | _ -> pp_modname kn

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

(** A type of a module-type concept's requirements, spelled from inside the
    concept ({!Modtype_concept.concept_type}). *)
let rec pp_concept_type : Modtype_concept.concept_type -> Pp.t = function
  | Member {member; enum; arguments} ->
    pp_member_type ~enum (global_name Type member) member
      (List.map pp_concept_type arguments)
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
let pp_requirement : Modtype_concept.requirement -> Pp.t = function
  | Inductive_member {member; enum; arity} ->
    let placeholders = List.init arity (fun _ -> pp_cpp_type false [] Tany) in
    pp_member_type ~enum (Cpp_name.unqualified (Common.pp_global_name Type member)) member placeholders ++ str ";" ++ fnl ()
  | Type_member {member; arity} ->
    let name = pp_global_name Type member in
    if arity = 0 then str "typename M::" ++ name ++ str ";" ++ fnl ()
    else
      str "typename M::template "
      ++ name
      ++ str "<"
      ++ prlist_with_sep (fun () -> str ", ") identity (List.init arity (fun _ -> str "void"))
      ++ str ">;"
      ++ fnl ()
  | Instance_member {value; class_; arguments} ->
    let name = pp_global_name Term value in
    writes_standard "concepts";
    str "typename M::"
    ++ name
    ++ str ";"
    ++ fnl ()
    ++ str "requires "
    ++ str (Common.pp_global_name Type class_)
    ++ str "<typename M::"
    ++ name
    ++ prlist (fun a -> str ", " ++ pp_concept_type a) arguments
    ++ str ">;"
    ++ fnl ()
  | Nullary_member {value; result} ->
    let name = pp_global_name Term value in
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
    let name = pp_global_name Term value in
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
    let concept_name = pp_concept_ref module_type in
    str "  requires "
    ++ concept_name
    ++ str "<typename M::"
    ++ str (Label.to_string label)
    ++ str ">;"
    ++ fnl ()

(** What a module type contributes where a concept body is expected
    ({!Modtype_concept.constraint_}), with the concepts of the module types
    nested in it, which are declared ahead of the concept it is the body of,
    innermost first.  An anonymous signature's requirements are printed with
    the signature and the functor parameters visible in it visible. *)
let rec pp_constraint : Modtype_concept.constraint_ -> Pp.t list * module_constraint = function
  | Named kn -> ([], MCname (pp_modname kn))
  | Requirements {signature; parameters; items} ->
    with_visibility (inside signature parameters (current_visibility ())) @@ fun () ->
    let item (hoisted, reqs) : Modtype_concept.item -> _ = function
      | Requirement req -> (hoisted, pp_requirement req :: reqs)
      | Nested (path, c) ->
        let inner, nested = pp_constraint c in
        let def = pp_concept_def (str (modtype_concept_name path)) (concept_body_pp nested) in
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

(** The declaration of the concept [name] of a module type, generated as
    [c], with the concepts its nested module types are hoisted into ahead of
    it.  The concept is over [M], the module it constrains, and over
    [params], the parameters of a functor declaring it, which its
    requirements may mention. *)
let pp_modtype_concept ?(params = []) name (c : Modtype_concept.t) =
  let head =
    str "template<typename M"
    ++ prlist (fun p -> str ", typename " ++ pp_modname p) params
    ++ str ">" ++ fnl ()
  in
  match c with
  | Alias {base; refinements} ->
    let base_args =
      prlist (fun p -> str ", " ++ pp_modname p) (concept_extra_args base)
    in
    head ++ str "concept " ++ name ++ str " = " ++ pp_concept_ref base
    ++ str "<M" ++ base_args ++ str ">"
    ++ prlist (fun c -> str " && " ++ c) (pp_refinements refinements)
    ++ str ";"
  | Constraint c ->
    let hoisted, body = pp_constraint c in
    prlist_with_sep (fun () -> fnl () ++ fnl ()) identity
      (hoisted @ [head ++ pp_concept_clause name (concept_body_pp body)])

(** The one spelling of "this subject satisfies this concept", on a line of
    its own. *)
let pp_assertion (a : Cpp_ast.assertion) =
  let concept =
    match a.concept with Of_module_type mp -> pp_concept_ref mp | Of_class r -> pp_concept_name_of_ref r
  in
  let subject =
    match a.subject with
    | Module m -> module_struct_name_of (resolved_module m)
    | Instance {instance; args} -> pp_global Type instance ++ prlist (fun ty -> str ", " ++ pp_cpp_type false [] ty) args
  in
  fnl () ++ str "static_assert(" ++ concept ++ str "<" ++ subject ++ str ">);"

