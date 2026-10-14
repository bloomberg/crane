(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Top-level C++ extraction orchestrator.

    This module handles module type → concept conversion, structure element
    processing, the wrapper module dual-pass, and the main pp_struct/pp_hstruct
    entry points. Lower-level rendering is delegated to:
    - {!Cpp_state} — mutable state and utilities
    - {!Cpp_names} — name resolution and qualification
    - {!Cpp_print} — type/expr/stmt/field/declaration pretty-printing
    - {!Cpp_ind} — inductive type rendering and decl-level dispatch *)

open Pp
open Util
open Names
open ModPath
open Table
open Miniml
open Common
open Minicpp
open Translation
open Gen_decls
open Cpp_state
open Cpp_names
open Cpp_print
open Cpp_ind

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

(** Run [f] while watching which global references it resolves, and report
    whether any came out qualified under [outer].

    That is what "this concept's requirements name the enclosing struct's own
    types" means.  It used to be asked of the finished text, by searching it
    for ["Outer::"], which also matched any identifier merely ending in
    [Outer]; asking the resolutions instead answers the question that was
    meant. *)
let watching_for_reference_to outer f =
  let seen = ref false in
  let saved = !Common.on_resolved in
  Common.on_resolved :=
    (fun r ->
      saved r;
      match List.filter (fun c -> c <> "") r.Common.rn_parts with
      | first :: _ :: _ when String.equal first outer -> seen := true
      | _ -> () );
  let result =
    Fun.protect ~finally:(fun () -> Common.on_resolved := saved) f
  in
  (result, !seen)

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

(** Convert a signature spec element to a C++20 [requires] clause requirement.
    Used for module type -> concept conversion.

    Each {!Miniml.ml_spec} variant maps to a different requirement:
    - [Sind]: [typename M::Name;] — checks that a nested type exists.
    - [Sval]: [{M::name(declval<A>(),...)} -> same_as<R>;] or the nullary
      form with [convertible_to].
    - [Stype] with empty [vl]: [typename M::Name;] — simple type member.
    - [Stype] with non-empty [vl]: [typename M::template Name<void,...>;]
      — validates a template alias member (higher-kinded type parameter
      such as [Parameter F : Type -> Type]).  The dummy [void] arguments
      serve only to check that the template exists with the correct arity;
      no semantic meaning is attached to the instantiation.

    @param modtype_mp    Module path of the enclosing module type; used to
                         decide whether a type reference is a member of [M]
                         (and should be qualified ["typename M::"]) or an
                         external type.
    @param modtype_refs  All type/inductive global refs declared directly in
                         the module-type signature; used to detect self-referential
                         member types without recursing into [modtype_mp].
    @return Pretty-printer document for the single requirement line, or [mt ()]
            if the spec should be suppressed (e.g. inline-custom, polymorphic
            value). *)
let rec pp_spec_as_requirement modtype_mp modtype_refs spec =
  (* The member type [name] of [M], a path to [r] from inside it, spelled as
     [r] is declared -- an enum capitalised -- and applied to [args] when it
     is a template. *)
  let member_type name r args =
    let name = if is_enum_cached r then capitalize_enum_qualified name r else name in
    match args with
    | [] -> str "typename M::" ++ str name
    | _ ->
      str "typename M::template " ++ str name ++ str "<"
      ++ prlist_with_sep (fun () -> str ", ") Fun.id args
      ++ str ">"
  in
  match spec with
  | Sval (r, _, _) when is_inline_custom r -> mt ()
  | Stype (r, _, _) when is_inline_custom r -> mt ()
  (* A record's projection is a data member of the record's struct, which
     [typename M::pt] already requires: a module emits no static function for
     it, and the functor body reads the field off the value. *)
  | Sval (r, _, _) when Table.is_projection r -> mt ()
  | Sind (kn, ind) ->
    (* A parameterised inductive is a class template, which only an
       instantiation names: any one will do, so the erased type. *)
    prvecti
      (fun i p ->
        let placeholders = List.map (fun _ -> pp_cpp_type false [] Tany) p.ip_vars in
        let r = GlobRef.IndRef (kn, i) in
        member_type (Common.pp_global_name Type r) r placeholders ++ str ";" ++ fnl () )
      ind.ind_packets
  | Sval (r, _, t) when has_tvar t -> mt ()
  | Sval (r, b, t) ->
    let name = pp_global_name Term r in
    let rec get_function_parts = function
      | Tarr (arg, rest) ->
        let args, ret = get_function_parts rest in
        (arg :: args, ret)
      | ret_ty -> ([], ret_ty)
    in
    let args, ret_ty = get_function_parts t in
    let cpp_ret =
      convert_ml_type_to_cpp_type (empty_env ()) [] ret_ty
    in
    let stdlib_ns = (sn ()).ns ^ "::" in
    let same_as = (sn ()).same_as in
    let declval = (sn ()).declval in
    let convertible_to = (sn ()).convertible_to in
    require_header "concepts";
    let rec is_mp_under base mp =
      ModPath.equal mp base
      || match mp with MPdot (parent, _) -> is_mp_under base parent | _ -> false
    in
    let rec get_base_mp = function
      | MPdot (parent, _) -> get_base_mp parent
      | mp -> mp
    in
    (* A parameter of a functor declaring the module type is an argument of
       the concept, named as itself. *)
    let is_functor_param_ref r =
      let b = get_base_mp (modpath_of_r r) in
      List.exists
        (fun (_, (_, params)) -> List.exists (ModPath.equal b) params)
        !functor_concept_scopes
    in
    let is_member_ref r =
      let rmp = modpath_of_r r in
      is_mp_under modtype_mp rmp
      || match get_base_mp rmp with
         | MPbound _ -> not (is_functor_param_ref r)
         | _ -> false
    in
    let rec qualify_type = function
      | Tglob (r, args, _) when not (is_custom r) && is_member_ref r ->
        member_type (Pp.string_of_ppcmds (pp_global Type r)) r (List.map qualify_type args)
      | Tglob (r, [], _) as t when not (is_custom r) && is_functor_param_ref r ->
        str "typename " ++ pp_cpp_type false [] t
      | Tglob (r, args, _) ->
        ( match find_custom_opt r with
        | Some custom_str ->
          qualify_custom_template
            (Foreign_template.custom_template_with_args custom_str (List.length args))
            args qualify_type
        | None ->
          ( match args with
          | [] -> pp_cpp_type false [] (Tglob (r, [], []))
          | _ ->
            pp_cpp_type false [] (Tglob (r, [], []))
            ++ str "<"
            ++ prlist_with_sep (fun () -> str ", ") qualify_type args
            ++ str ">" ) )
      | Tshared_ptr ty ->
        str stdlib_ns ++ str "shared_ptr<" ++ qualify_type ty ++ str ">"
      | Tvariant (Inline_variant, tys) ->
        str stdlib_ns
        ++ str "variant<"
        ++ prlist_with_sep (fun () -> str ", ") qualify_type tys
        ++ str ">"
      | Tvariant (Shared_variant, tys) ->
        str Crane_rt.shared_variant
        ++ str "<"
        ++ prlist_with_sep (fun () -> str ", ") qualify_type tys
        ++ str ">"
      | Tnamespace (r, Tglob (r', args, e)) when not (is_member_ref r) ->
        ( match args with
        | [] -> pp_cpp_type false [] (Tnamespace (r, Tglob (r', [], e)))
        | _ ->
          pp_cpp_type false [] (Tnamespace (r, Tglob (r', [], e)))
          ++ str "<"
          ++ prlist_with_sep (fun () -> str ", ") qualify_type args
          ++ str ">" )
      | Tnamespace (r, ty) ->
        if is_member_ref r then qualify_type ty
        else pp_cpp_type false [] (Tnamespace (r, ty))
      | Tfun (d, c) ->
        (* Function-type argument: qualify member types inside the function
           signature.  Without this case, (elt -> bool) would fall through to
           pp_cpp_type and render as crane::fn<bool(elt)> — elt is bare.
           We need crane::fn<bool(typename M::elt)>. *)
        Table.demand_header (Table.Runtime Crane_rt.fn_header);
        str Crane_rt.fn ++ str "<"
        ++ qualify_type c
        ++ str "("
        ++ prlist_with_sep (fun () -> str ", ") qualify_type d
        ++ str ")>"
      | ty -> pp_cpp_type false [] ty
    in
    (* A parameter whose type is a type class names an {e instance}, and Crane
       emits an instance as a nested struct that satisfies the class's concept.
       Ask for the member type and constrain it: a concept name is not a type,
       so the value form below would spell [convertible_to<Weigh<...>>], which
       does not compile. *)
    begin match ret_ty with
    | Tglob (cls, cls_args, _) when args = [] && Table.is_typeclass cls ->
      str "typename M::"
      ++ name
      ++ str ";"
      ++ fnl ()
      ++ str "requires "
      ++ str (Common.pp_global_name Type cls)
      ++ str "<typename M::"
      ++ name
      ++ prlist
           (fun a ->
             str ", "
             ++ qualify_type
                  (convert_ml_type_to_cpp_type (empty_env ()) [] a) )
           cls_args
      ++ str ">;"
      ++ fnl ()
    | _ ->
    if args = [] then
      (* A nullary module value may be emitted either as a static data member
         ([M::name]) or, inside a template where it becomes a Meyers singleton,
         as a nullary accessor function ([M::name()]).  Which spelling a functor
         body uses is decided later (by the [template_static_accessors] registry
         and per-reference resolution) and is not reliably knowable here at
         concept-generation time.  Accept BOTH forms so the concept never
         rejects a module a generated body would in fact accept; the requirement
         still enforces that the member exists with a convertible result type. *)
      let qualified_ret = qualify_type cpp_ret in
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
    else
      let cpp_args =
        List.map
          (convert_ml_type_to_cpp_type (empty_env ()) [])
          args
      in
      let declvals =
        List.map
          (fun arg_ty ->
            str declval ++ str "<" ++ qualify_type arg_ty ++ str ">()" )
          cpp_args
      in
      let call_expr =
        str "M::"
        ++ name
        ++ str "("
        ++ prlist_with_sep (fun () -> str ", ") identity declvals
        ++ str ")"
      in
      str "{ "
      ++ call_expr
      ++ str " } -> "
      ++ str same_as
      ++ str "<"
      ++ qualify_type cpp_ret
      ++ str ">;"
      ++ fnl ()
    end
  | Stype (r, vl, ot) ->
    let name = pp_global_name Type r in
    if vl = [] then
      str "typename M::" ++ name ++ str ";" ++ fnl ()
    else
      (* Higher-kinded type parameter: check template alias exists by
         instantiating with dummy void arguments *)
      let dummy_args = List.map (fun _ -> str "void") vl in
      str "typename M::template "
      ++ name
      ++ str "<"
      ++ prlist_with_sep (fun () -> str ", ") identity dummy_args
      ++ str ">;"
      ++ fnl ()

(** Render a concept name from a module path reference.  In separate extraction,
    concepts live inside their own namespace, so cross-file references need
    qualification.  For a top-level module type [X] that is its own extraction
    unit, the C++ structure is [namespace X { concept X = ...; }], requiring
    [X::X] from outside. *)
and pp_concept_ref kn =
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

         Compare mp0 against the file-level MPfile of the current context,
         not top_visible_mp() — the latter may be an MPdot (e.g. inside a
         module-type body) even when the concept is in the same file. *)
      let rec get_file_mp = function
        | ModPath.MPfile _ as mp -> mp
        | ModPath.MPdot (mp, _) -> get_file_mp mp
        | ModPath.MPbound _ -> mp0  (* functor param scope — treat as same *)
      in
      let current_file_mp = get_file_mp (top_visible_mp ()) in
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

(** Convert a module type to a C++20 concept. MTsig generates requires clauses,
    MTfunsig is handled by param tracking, MTident references an existing
    concept by name.

    @param params  Accumulated list of bound module-path parameters introduced
                   by enclosing [MTfunsig] binders.  These are pushed onto the
                   visibility stack when an [MTsig] body is entered so that
                   functor-parameter references resolve correctly.
    @return The concept name the module type refers to, or the requirement
            lines an anonymous signature contributes. *)
and pp_module_type params = function
  | MTident kn -> MCname (pp_modname kn)
  | MTfunsig (mbid, mt, mt') -> pp_module_type (MPbound mbid :: params) mt'
  | MTsig (mp, sign) ->
    push_visible mp params;
    let modtype_refs =
      List.fold_left
        (fun acc (_label, specif) ->
          match specif with
          | Spec (Stype (r, _, _)) -> r :: acc
          | Spec (Sind (kn, _)) -> GlobRef.IndRef (kn, 0) :: acc
          | _ -> acc )
        []
        sign
    in
    let pp_req (label, specif) =
      match specif with
      | Spec s -> pp_spec_as_requirement mp modtype_refs s
      | Smodule mod_type ->
        ( match mod_type with
        | MTident kn ->
          let concept_name = pp_concept_ref kn in
          let label_name = Label.to_string label in
          str "  requires "
          ++ concept_name
          ++ str "<typename M::"
          ++ str label_name
          ++ str ">;"
          ++ fnl ()
        | MTfunsig _ -> mt ()
        | _ -> mt () )
      | Smodtype nested_mt ->
        let def = concept_body_pp (pp_module_type [] nested_mt) in
        let modtype_name = str (modtype_concept_name (MPdot (mp, label))) in
        let concept_pp = pp_concept_def modtype_name def in
        hoisted_concept_defs := concept_pp :: !hoisted_concept_defs;
        mt ()
    in
    let reqs = List.map pp_req sign in
    let reqs = List.filter (fun p -> not (Pp.ismt p)) reqs in
    pop_visible ();
    MCrequirements reqs
  | MTwith (mt, ML_With_type (idl, vl, typ)) -> pp_module_type [] mt
  | MTwith (mt, ML_With_module (idl, mp)) -> pp_module_type [] mt

(** Format a doc comment string as [///] comment lines. Translates bracket
    references [[name]] by stripping the brackets. Returns [mt ()] if no doc
    comment is found for the given name. *)
let pp_doc_comment_for_name name =
  match Doc_comments.find name with
  | None -> mt ()
  | Some text ->
    let lines = Doc_comments.format_as_cpp_lines text in
    prlist_with_sep fnl (fun l -> str l) lines ++ fnl ()

(** Look up and format a doc comment for the given label. *)
let pp_doc_comment label = pp_doc_comment_for_name (Label.to_string label)

(** Whether the first printable content in [p] is a C++ doc comment.  Soft
    breaks are ignored because they may be flattened to nothing. *)
let starts_with_doc_comment p =
  let rec first_output = function
    | [] -> None
    | p :: rest ->
      ( match Pp.repr p with
      | Ppcmd_empty | Ppcmd_print_break _ -> first_output rest
      | Ppcmd_string text -> Some (String.starts_with ~prefix:"///" text)
      | Ppcmd_glue parts ->
        ( match first_output parts with
        | Some _ as result -> result
        | None -> first_output rest )
      | Ppcmd_box (_, contents) | Ppcmd_tag (_, contents) ->
        ( match first_output [contents] with
        | Some _ as result -> result
        | None -> first_output rest )
      | Ppcmd_force_newline | Ppcmd_comment _ -> Some false )
  in
  match first_output [p] with Some result -> result | None -> false

(** Join already-rendered structure elements, forcing a newline before a
    leading C++ doc comment.  [cut2] normally supplies soft breaks for
    clang-format, but an unbroken [}///] or [;///] is interpreted as a trailing
    comment and cannot be repaired by the formatter. *)
let rec prlist_with_doc_safe_sep sep = function
  | [] -> mt ()
  | [p] -> p
  | p :: ((next :: _) as rest) ->
    let boundary =
      if starts_with_doc_comment next then fnl () else sep ()
    in
    p ++ boundary ++ prlist_with_doc_safe_sep sep rest

(** Try to extract a named concept from a module type.

    Strips [MTwith] constraints (which have no C++ concept equivalent) and
    [MTfunsig] parameter layers, looking for an [MTident] that references an
    already-defined concept.  Returns [None] for anonymous inline signatures
    ([MTsig]).

    This is important for functor parameters like
    [c' : C b' with Module a := A_instance].  Rocq's extraction expands
    [MEapply] (module type application) into an inline [MTsig], losing the
    reference to the named concept [C].  Without this helper,
    [pp_module_type] would inline the concept body into the template
    parameter list, producing garbled C++. *)
let rec concept_of_mt = function
  | MTident kn -> Some (kn, pp_concept_ref kn)
  | MTwith (mt, _) -> concept_of_mt mt
  | MTfunsig (_, _, mt') -> concept_of_mt mt'
  | MTsig _ -> None

(** The one spelling of "this struct satisfies this concept".  Both the
    immediate assertion and the deferred one go through here, so the two cannot
    drift apart. *)
let pp_concept_assert concept subject =
  fnl () ++ str "static_assert(" ++ concept ++ str "<" ++ subject ++ str ">);"

(** The assertion that the module rendered as [name] satisfies the concept of
    its module type [mty].  When that concept is one the enclosing struct holds
    back, so is the assertion: the concept is not declared yet. *)
let concept_assert_pp name mty =
  match concept_of_mt mty with
  | None -> mt ()
  | Some (mt_mp, concept_name) ->
    let held = HCmodtype mt_mp in
    if concept_held_back held then (
      deferred_concept_asserts :=
        (held, concept_name, name) :: !deferred_concept_asserts;
      mt () )
    else pp_concept_assert concept_name name

(** Like {!concept_of_mt}, but returns the base module type's raw
    kernel name (for callers that emit [Name<M>] directly rather than a
    pretty-printed concept reference). *)
let rec get_base_concept = function
  | MTident kn -> Some kn
  | MTwith (mt, _) -> get_base_concept mt
  | _ -> None

(** Render the [MTwith] refinements of a module type ([BASE with Definition t
    := nat], [OUTER with Module Inner := NatInner]) as C++ [std::same_as<…>]
    constraints.

    A refined module type such as [NAT_BASE := BASE with Definition t := nat]
    would otherwise be emitted as a bare alias [concept NAT_BASE = BASE<M>;],
    silently dropping the [t := nat] equality so any module satisfying [BASE]
    is accepted — including ones whose [t] is not [nat] (CWE-345 / CWE-807).
    Emitting [std::same_as<typename M::t, uint64_t>] as an extra conjunct
    restores that fixed-type / fixed-submodule requirement at the concept
    boundary.  Returns the constraint documents (one per refinement); the
    caller conjoins them onto the base concept. *)
let collect_with_refinements mt =
  let rec go acc = function
    | MTwith (inner, ML_With_type (idl, _vl, typ)) ->
      let path = String.concat "::" (List.map Id.to_string idl) in
      let cpp = convert_ml_type_to_cpp_type (empty_env ()) [] typ in
      let clause =
        str (sn ()).same_as
        ++ str "<typename M::"
        ++ str path
        ++ str ", "
        ++ pp_cpp_type false [] cpp
        ++ str ">"
      in
      go (clause :: acc) inner
    | MTwith (inner, ML_With_module _) ->
      (* [with Module Inner := Concrete] would need a [std::same_as<typename
         M::Inner, Concrete>] check, but the concept is emitted at namespace
         scope before the concrete module's struct is declared, so a forward
         reference to it does not compile.  Leave the submodule refinement
         unenforced (as before) rather than emit a broken constraint. *)
      go acc inner
    | _ -> acc
  in
  let clauses = go [] mt in
  if clauses <> [] then require_header "concepts";
  clauses

(** The declaration of the concept [name] a module type [m] becomes, with the
    concepts its nested module types are hoisted into ahead of it.  The
    concept is over [M], the module it constrains, and over [params], the
    parameters of a functor declaring it, which its requirements may
    mention. *)
let pp_modtype_concept ?(params = []) name m =
  let head =
    str "template<typename M"
    ++ prlist (fun p -> str ", typename " ++ pp_modname p) params
    ++ str ">" ++ fnl ()
  in
  match get_base_concept m with
  | Some base_kn ->
    let base_args =
      prlist (fun p -> str ", " ++ pp_modname p) (concept_extra_args base_kn)
    in
    head ++ str "concept " ++ name ++ str " = " ++ pp_concept_ref base_kn
    ++ str "<M" ++ base_args ++ str ">"
    ++ prlist (fun c -> str " && " ++ c) (collect_with_refinements m)
    ++ str ";"
  | None ->
    let hoisted, def =
      collecting hoisted_concept_defs (fun () ->
          concept_body_pp (pp_module_type params m) )
    in
    prlist_with_sep (fun () -> fnl () ++ fnl ()) identity
      (hoisted @ [head ++ pp_concept_clause name def])

(** Render a functor parameter as a C++ template parameter.

    Strategy:
    - If a named concept can be extracted from the module type via
      {!concept_of_mt}, emit [ConceptName param_name].
    - Otherwise emit [typename param_name] (unconstrained type parameter).
      {!concept_of_mt} declines only for [MTsig], and an anonymous
      signature's requirement lines are not a constraint expression: they
      belong inside a named concept, not in a template parameter list. *)
let pp_template_param (mbid, mt) =
  let param_name = pp_modname (MPbound mbid) in
  match concept_of_mt mt with
  (* A concept the enclosing struct holds back is declared after it, so a
     functor inside it takes its parameter unconstrained, as a class concept
     held back does. *)
  | Some (mt_mp, _) when concept_held_back (HCmodtype mt_mp) -> str "typename " ++ param_name
  | Some (mt_mp, cname) ->
    let args =
      match concept_extra_args mt_mp with
      | [] -> Pp.mt ()
      | ps -> str "<" ++ prlist_with_sep (fun () -> str ", ") pp_modname ps ++ str ">"
    in
    cname ++ args ++ str " " ++ param_name
  | None ->
    (* Rendered for its side effects: nested module types are hoisted out of
       the signature as concepts of their own. *)
    ignore (pp_module_type [] mt : module_constraint);
    str "typename " ++ param_name

(** The lifted helper a declaration defines, if it defines one, used to emit it
    only once.

    Asking {!Lifted.of_ref} rather than matching the shape of the name is what
    keeps an ordinary [Dfun] whose reference happens to be a [VarRef] -- a
    record field accessor, a [make] factory -- from being mistaken for a
    helper and deduplicated against one. *)
let rec lifted_decl_key = function
  | Dtemplate (_, _, inner) -> lifted_decl_key inner
  | Dfun {df_path = {dp_outer = r, []; dp_inner = []}; _} ->
    Option.map Lifted.name (Lifted.of_ref r)
  | _ -> None

let dedup_lifted_decls ds =
  let seen = Hashtbl.create 16 in
  List.filter
    (fun d ->
      match lifted_decl_key d with
      | Some k ->
        if Hashtbl.mem seen k then false else (Hashtbl.replace seen k (); true)
      | None -> true )
    ds

(** Whether [spec] may be emitted at the top of the file, above every
    definition in it.

    A declaration needs the types in its signature {e declared}, not complete,
    which is what lets one naming [Nat] precede [Nat]'s own definition.  Naming
    [List::list] is a different act: it is name lookup {e into} [List], and
    that needs [List] complete.  A forward declaration cannot supply it, so no
    position above the structs is legal for such a signature and the honest
    answer is to leave it where it is.

    Decided by reading the rendered declaration, because the question is about
    the text and nothing else can answer it without disagreeing.  The IR node
    cannot: [Nat] and [List::list] are both [Tnamespace], which means "an
    inductive's own scope", not "inside a module struct".  Nor can the tables
    behind the printer, taken one at a time -- whether a qualifier is written
    is settled by a chain of them (is the module a wrapper, is the type
    nonetheless emitted at global scope, is it an eponymous record, an enum, a
    local inductive), and any single one of them is a second opinion.  Two
    such opinions have already been wrong here.

    [std::] is the one qualifier that needs nothing complete: it names into a
    namespace, not a struct, and the standard library is included above
    everything.  Every other qualifier is refused, including a dependent
    [M::t], which needs no completeness but costs only a missed hoist to
    refuse.

    This is the one place a declaration is not free.  A helper declared
    needlessly costs a line, but a helper declared needlessly {e and}
    qualifying into a struct would drag the whole block below that struct --
    past the uses it exists to precede -- so what it costs is the position, for
    every other helper in the block. *)
let spec_names_into_a_struct (rendered : string) : bool =
  let n = String.length rendered in
  let is_ident c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    || c = '_'
  in
  let rec scan i =
    if i + 1 >= n then false
    else if rendered.[i] = ':' && rendered.[i + 1] = ':' then
      let stop = ref i in
      while !stop > 0 && is_ident rendered.[!stop - 1] do decr stop done;
      let qualifier = String.sub rendered !stop (i - !stop) in
      if String.equal qualifier "std" then scan (i + 2) else true
    else scan (i + 1)
  in
  scan 0

let spec_is_hoistable (spec : Cpp_erasure.settled) : bool =
  not
    (spec_names_into_a_struct
       (Pp.string_of_ppcmds (pp_cpp_decl (empty_env ()) spec)) )

(** A lifted helper [d], finalized: what to write in its place, and the
    declaration to hoist ahead of its callers where [d] defines a function,
    [may_hoist] allows it, and {!spec_is_hoistable} does.

    Both come from one finished definition, so the hoisted declaration states
    the head the definition does; the definition then leaves the template
    defaults to the declaration. *)
let lifted_views ?(may_hoist = true) (d : cpp_decl) =
  let e = Function_entity.finalize d in
  let spec = Function_entity.declaration e in
  if Function_entity.defines_function e && may_hoist && spec_is_hoistable spec
  then (Function_entity.definition_after_declaration e, Some spec)
  else (Function_entity.definition e, None)

(** Whether a module's members name only types a forward declaration can
    stand in for.

    The header opens with a forward declaration of every datatype struct, so a
    parameter or result spelled at one is nameable from anywhere in the file.
    Anything else a member's type can name -- a Rocq definition used as a type,
    which reaches C++ as a [using] alias at the point it was defined -- is not.

    Read off the members' ML types rather than the rendered text, because the
    text cannot tell [tbl] the alias from [a] the parameter. *)
let module_members_name_only_inductives sel =
  let rec ty_ok = function
    | Miniml.Tglob (r, args, _) ->
      (match r with GlobRef.IndRef _ -> true | _ -> false)
      && List.for_all ty_ok args
    | Miniml.Tarr (a, b) -> ty_ok a && ty_ok b
    | Miniml.Tmeta {contents = Some t} -> ty_ok t
    | _ -> true
  in
  List.for_all
    (fun (_, se) ->
      match se with
      | SEdecl ((Dterm _ | Dfix _) as d) ->
        List.for_all (fun fd -> ty_ok fd.fd_type) (Mlutil.term_defs d)
      (* Only a function declaration is being judged here.  Everything else a
         module holds -- an inductive, a type alias, a submodule -- is either
         rendered somewhere other than this struct or shows up in its text as a
         member that is not a [static] declaration, which the other half
         rejects; asking a question about it here only rejects modules whose
         struct never contained it. *)
      | _ -> true )
    sel

(** Whether a module's struct may be declared ahead of the file rather than at
    the module's own place in the emitted order.

    Its own place is the safe answer and stays the default, because a member
    initialised inside the struct body runs there, and everything that body
    names must be complete by then.  The one shape that is certainly free of
    that is a struct of nothing but static function {e declarations} --
    [static Nat pick(Nat, Nat);], defined out of line: a declaration asks its
    parameter and result types to be declared, which the forward declarations
    above already do, and asks nothing else of the file at all.  So the only
    thing such a struct's position decides is whether its callers can see it,
    and a function hoisted onto a datatype is a caller emitted with the
    datatype, which may come first.

    This half is read off the rendered struct, because that text is what the
    compiler reads: every member must be a [static] declaration ending at its
    semicolon -- no body, no initialiser, no alias, no data, no nested type --
    the struct must not be a template, and no name may be qualified into
    another struct, which is the question {!spec_is_hoistable} asks of a lifted
    helper and for the same reason: [Other::t] needs [Other] complete, so
    moving this in front of it would not help.  The other half, which the text
    cannot answer, is {!module_members_name_only_inductives}. *)
let module_struct_is_hoistable rendered =
  match (String.index_opt rendered '{', String.rindex_opt rendered '}') with
  | Some o, Some c when o < c ->
    let head = String.sub rendered 0 o in
    let body = String.sub rendered (o + 1) (c - o - 1) in
    let members = String.split_on_char ';' body in
    let is_static_decl m =
      let m = String.trim m in
      m = ""
      || (String.length m > 7
         && String.equal (String.sub m 0 7) "static "
         && String.contains m '('
         && not (String.contains m '='))
    in
    let is_template =
      let n = String.length head in
      let rec scan i =
        i + 8 <= n
        && (String.equal (String.sub head i 8) "template" || scan (i + 1))
      in
      scan 0
    in
    (not (String.contains body '{'))
    && (not is_template)
    && (not (spec_names_into_a_struct rendered))
    && List.for_all is_static_decl members
  | _ -> false

(** The module structs this file's pass chose to declare ahead of everything,
    newest first.  Emptied by the assembly at the end of
    {!do_struct_with_decl_tracking}. *)
let hoisted_module_structs : Pp.t list ref = ref []

(** Report what a lifted helper met at the site that placed it, under
    [CRANE_DBG_LIFTED].

    A helper comes back from the generation that lifted it to the site that
    places that generation, and which of the site's conditions it failed is
    not recoverable from the output.

    The rendered declaration is printed with it, because that text is what
    {!spec_is_hoistable} reads: a rejection is only interpretable next to the
    qualifier that caused it. *)
let dbg_lifted =
  let on = lazy (Sys.getenv_opt "CRANE_DBG_LIFTED" <> None) in
  fun ~site ?(extra = "") (d : cpp_decl) ->
    if Lazy.force on then
      let name =
        match lifted_decl_key d with
        | Some k -> Id.to_string k
        | None -> "<not-a-lifted-helper>"
      in
      let split =
        let e = Function_entity.finalize d in
        if Function_entity.defines_function e then
          let spec = Function_entity.declaration e in
          Printf.sprintf "splits=yes hoistable=%b spec=%S"
            (spec_is_hoistable spec)
            (Pp.string_of_ppcmds (pp_cpp_decl (empty_env ()) spec))
        else "splits=no"
      in
      Feedback.msg_notice
        (Pp.str
           (Printf.sprintf "[crane:lifted] %-28s site=%-12s %s%s" name site
              split
              (if extra = "" then "" else " " ^ extra) ) )

(** The declarations of helpers lifted out of a declaration that is not a
    wrapper module's -- an inductive's own, whose helpers {!pp_structure_elem}
    emits directly after the struct closes, and so after the methods that call
    them.  They are due at the top of the file like every other lifted
    helper's, so they are deferred, with their scope, for the file to
    collect. *)
let pending_lifted_specs = Cpp_ind.deferred "pending_lifted_specs"

(** Lifted helpers already emitted as members of the struct being rendered. *)
let emitted_member_lifted : (Id.t, unit) Hashtbl.t = Hashtbl.create 16

(** The concept of the type class [r], recorded as [r]'s generation. *)
let generated_concept r fields =
  let d = Gen_decls.gen_typeclass_cpp r fields in
  ignore (record_entity r [d] []);
  d

(** The methods of the eponymous record [r] made of [candidates], each
    recorded as the generation of the function it was made of, and the
    helpers lifted out of their bodies, which are members beside them. *)
let generated_record_methods r vars candidates =
  let fields, lifted =
    Translation.collecting_lifted (fun () -> Gen_decls.gen_record_methods r vars candidates)
  in
  List.iter
    (fun ((f, _, _) as field) ->
      ignore
        ( match f with
        | Fmethod {mf_globref = Some m; _} ->
          let own d =
            match Option.bind (decl_globref d) Lifted.of_ref with
            | Some h -> Option.equal Names.GlobRef.UserOrd.equal (Lifted.origin h) (Some m)
            | None -> false
          in
          Some
            (record_entity m
               [ Dfields
                   { ds_ref = r;
                     ds_fields = [field];
                     ds_tparams = [];
                     ds_constraint = None;
                     ds_needs_shared_from_this = false } ]
               (List.filter own lifted) )
        | _ -> None ) )
    fields;
  (fields, lifted)

(** Pretty-print a structure element (label, elem) pair. Handles modules, module
    types, and declarations.

    @param is_header  When [true], emit header-mode output (struct definitions,
                      concept declarations, [using] aliases).  When [false],
                      emit implementation-mode output (out-of-line function
                      bodies, skipping header-only constructs).
    @param f          Callback used to pretty-print individual {!Miniml.ml_decl}
                      nodes; typically [impl_decls] or [header_decls].
    @return Pretty-printer document for the element, or [mt ()] if the element
            produces no output in the current pass. *)
let rec pp_structure_elem ~is_header f = function
  | l, SEdecl d ->
    (* {b Placement of lifted lambda helpers.}  A helper lifted out of a local
       [let g := fun ... in] that mentions the enclosing struct (its parameter
       types, or a sibling definition it calls) cannot be emitted before that
       struct, and emitting it after leaves the call site — which sits in a
       static data member initializer, {i not} a complete-class context —
       referring to an undeclared name.  Emit it as a static member template
       right before the declaration that produced it instead; helpers produced
       elsewhere keep their file-scope placement. *)
    let {Cpp_ind.rendered; helpers} = f d in
    (* An erasure landing pad -- [using X = std::any;] -- travels to the very
       top of the file, ahead of the concepts.

       It is correct there because it names nothing: the right-hand side is
       [std::any] and the parameters, if any, are its own.  It is {e needed}
       there because the text that lands on it does not follow it.  A concept
       body spells such a name bare, and concepts are hoisted to the top by the
       case below, so leaving the alias where it was written puts the use in
       front of the declaration.  Hoisting both and ordering them here is what
       makes that pair of placements independent of each other, and of any
       later pass that reorders the file. *)
    let is_erased_alias (_, d) =
      match (d : Cpp_erasure.settled :> cpp_decl) with
      | Dusing {du_rhs = Some rhs; _} -> Cpp_erasure.is_any_shaped rhs
      | _ -> false
    in
    let body =
      if
        is_header
        && (not (!render_ctx).rc_in_struct)
        && rendered <> []
        && List.for_all is_erased_alias rendered
      then (
        Cpp_ind.defer Cpp_ind.file_scope_erased_aliases rendered;
        mt () )
      else pp_decls rendered
    in
    (* A type class rendered at file scope is a concept, and a concept has no
       forward declaration to bridge a use that precedes it.  One such use is
       written unconditionally: a lifted helper's spec goes ahead of every
       section, because its callers are members of the struct it came out of,
       and its constraint names this concept.  So the concept travels to the
       top of the file, where the concepts of a nested module's type classes
       already go.

       Only at file scope: inside a struct the concept has already been
       hoisted or held back by {!pp_structure_elements}, which knows which of
       those two it is and this does not. *)
    let body =
      if
        is_header
        && (not (!render_ctx).rc_in_struct)
        && (not (!render_ctx).rc_concepts_hoisted)
        && (match d with
           | Miniml.Dind (_, ind) -> (
             match ind.ind_kind with Miniml.TypeClass _ -> true | _ -> false )
           | _ -> false)
        && not (Pp.ismt body)
      then (
        push file_scope_concepts (pp_doc_comment l ++ body);
        mt () )
      else
        body
    in
    let member_lifted =
      if not is_header then mt ()
      else
        let lifted =
          helpers
          |> dedup_lifted_decls
          |> List.filter (fun d' ->
                 match lifted_decl_key d' with
                 | Some k ->
                   if Hashtbl.mem emitted_member_lifted k then false
                   else (Hashtbl.replace emitted_member_lifted k (); true)
                 | None -> true )
        in
        List.fold_left
          (fun acc d' ->
            (* Emitted after the struct this was lifted out of, so after the
               methods that call it.  The definition stays where it is and the
               declaration is left for the file to put at the top -- the same
               repair as for a wrapper module's lifted helpers, on the path
               that produces them one at a time into a [Pp.t]. *)
            dbg_lifted ~site:"structure-elem"
              ~extra:
                (Printf.sprintf "rc_in_struct=%b" (!render_ctx).rc_in_struct)
              d';
            (* Only at namespace scope.  A struct is a complete-class
               context, so a method may call a member declared after it and a
               member has no forward reference to repair -- this pass has
               nothing to do there, whatever would be legal.

               Legality says the same thing the one time it is asked: a
               member's signature resolves against the struct, a nested [t] or
               a sibling type, and hoisting the declaration to file scope takes
               those names out of scope with it. *)
            let def, spec =
              lifted_views ~may_hoist:(not (!render_ctx).rc_in_struct) d'
            in
            Option.iter
              (fun spec -> Cpp_ind.defer pending_lifted_specs [(empty_env (), spec)])
              spec;
            let pp = pp_cpp_decl (empty_env ()) def in
            if Pp.ismt pp then acc
            else if Pp.ismt acc then pp
            else acc ++ cut2 () ++ pp )
          (mt ())
          lifted
    in
    let body =
      if Pp.ismt member_lifted then body
      else if Pp.ismt body then member_lifted
      else
        (* A helper lifted out of an inductive's own declaration comes from a
           definition that was turned into a method of that inductive, so it
           names the inductive in its parameter types and must follow it.  Its
           call sites are method bodies, which are complete-class contexts and
           so may name a member declared later. *)
        match d with
        | Miniml.Dind _ -> body ++ cut2 () ++ member_lifted
        | _ -> member_lifted ++ cut2 () ++ body
    in
    if Pp.ismt body then
      mt ()
    else
      pp_doc_comment l ++ body
  | l, SEmodule m ->
    let mp = MPdot (top_visible_mp (), l) in
    let name =
      match m.ml_mod_expr with
      | MEident _ | MEapply _ ->
        (* Transparent aliases generate a [using X = Y;] alias in C++.
           Calling [pp_modname mp] would call [add_visible (Mod, s) l], which
           marks this short name as "in scope" and triggers a spurious
           [error_module_clash] when two modules at different nesting depths
           share the same short name (e.g. a top-level [Module Impl] and an
           inner [Module Impl := ...] inside a functor body).  Since aliases
           don't introduce new identifiers into the qualified-name namespace,
           we compute the name without registering it -- the name references
           spell, a renamed one where another module shares the label
           ([OrdersEx.Positive_as_OT] beside [OrderedTypeEx.Positive_as_OT]). *)
        let s = Common.emitted_module_name mp in
        str (Table.escape_reserved_struct_name s)
      | _ ->
        let raw = pp_modname mp in
        let s = Pp.string_of_ppcmds raw in
        let escaped = Table.escape_reserved_struct_name s in
        if String.equal s escaped then raw else str escaped
    in
    (* A submodule becomes a nested struct, which shadows any global-scope type
       of the same name for unqualified lookups from inside the parent -- a
       [Module Nat] hides the runtime [Nat] exactly as an [Inductive Nat]
       would.  Record it so {!Cpp_names.global_scope_qualifier_for} spells the
       global one [::Nat]. *)
    if (!render_ctx).rc_in_struct then
      add_nested_struct_name (Pp.string_of_ppcmds name) (NSmodule mp);
    let mod_pp =
      match m.ml_mod_expr with
      | MEfunctor _ ->
        if not is_header then
          mt ()
        else
          let get_template_and_body = function
            | MEfunctor (mbid, mt, me) ->
              let rec collect_params mbid mt me =
                match me with
                | MEfunctor (mbid', mt', me') ->
                  let params_rest, body = collect_params mbid' mt' me' in
                  ((mbid, mt) :: params_rest, body)
                | _ -> ([(mbid, mt)], me)
              in
              collect_params mbid mt me
            | _ -> ([], m.ml_mod_expr)
          in
          let template_params, body = get_template_and_body m.ml_mod_expr in
          (* The module types the body declares cannot be concepts inside the
             class template the functor becomes: they go to file scope, over
             the functor's parameters too, under the functor's name. *)
          ( match body with
          | MEstruct (body_mp, sel) ->
            let params = List.map (fun (mbid, _) -> MPbound mbid) template_params in
            List.iter
              (function
                | l, SEmodtype mty ->
                  push file_scope_concepts
                    (pp_modtype_concept ~params (pp_concept_ref (MPdot (body_mp, l))) mty)
                | _ -> () )
              sel
          | _ -> () );
          let template_decl =
            str "template<"
            ++ prlist_with_sep
                 (fun () -> str ", ")
                 pp_template_param
                 template_params
            ++ str ">"
          in
          let struct_body =
            with_render_ctx
              (fun c -> { c with rc_in_struct = true; rc_in_template = true })
              (fun () ->
                pp_module_expr
                  ~is_header
                  f
                  (List.map (fun (mbid, _) -> MPbound mbid) template_params)
                  body )
          in
          (match body with
          | MEapply _ ->
            template_decl
            ++ fnl ()
            ++ str "struct "
            ++ name
            ++ str " : "
            ++ struct_body
            ++ str " {};"
          | _ ->
            template_decl
            ++ fnl ()
            ++ str "struct "
            ++ name
            ++ str " {"
            ++ fnl ()
            ++ struct_body
            ++ str "};")
      | MEapply _ ->
        if not is_header then
          mt ()
        else
          let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
          let using_decl =
            str "using " ++ name ++ str " = " ++ body ++ str ";"
          in
          using_decl ++ concept_assert_pp name m.ml_mod_type
      | MEstruct (_mp, sel) ->
        let old_context = (!render_ctx).rc_in_struct in
        with_module_frame @@ fun () ->
        let module_name_str = Pp.string_of_ppcmds name in
        let lowercase_module = String.lowercase_ascii module_name_str in
        List.iter
          (fun (_l, se) ->
            match se with
            | SEdecl (Dind (kn, ind)) ->
              Array.iteri
                (fun i p ->
                  let ind_ref = GlobRef.IndRef (kn, i) in
                  let ind_name = Common.pp_global_name Type ind_ref in
                  if String.lowercase_ascii ind_name = lowercase_module then
                    match
                      ind.ind_kind
                    with
                    | TypeClass _ -> ()
                    | Record fields ->
                      (* Registered up front from
                         {!Structure_analysis.eponymous_records}; here we only
                         need it as the module currently being rendered. *)
                      eponymous_record := Some (ind_ref, fields, p)
                    | _ -> eponymous_type_ref := Some ind_ref )
                ind.ind_packets
            | _ -> () )
          sel;
        method_candidates := [];
        let epon_ref_opt =
          match (!eponymous_type_ref, !eponymous_record) with
          | Some r, _ -> Some r
          | _, Some (r, _, _) -> Some r
          | None, None -> None
        in
        ( match epon_ref_opt with
        (* A custom type has no struct of Crane's, and an enum is an [enum
           class]: neither can hold a method, as the registry's own scan
           already says. *)
        | Some epon_ref when not (is_custom epon_ref || Table.is_enum_inductive epon_ref) ->
          let epon_modpath = modpath_of_r epon_ref in
          let same_module r = ModPath.equal (modpath_of_r r) epon_modpath in
          let module_type_aliases =
            ref (Method_registry.collect_module_type_aliases
                   ~extract_decl:(fun (_l, se) ->
                     match se with SEdecl d -> Some d | _ -> None)
                   epon_modpath sel)
          in
          let forward_inductives = ref [] in
          let seen_epon = ref false in
          List.iter
            (fun (_l, se) ->
              match se with
              | SEdecl (Dind (fwd_kn, fwd_ind)) ->
                Array.iteri
                  (fun j _p ->
                    let fwd_ref = GlobRef.IndRef (fwd_kn, j) in
                    if globref_equal fwd_ref epon_ref
                    then
                      seen_epon := true
                    else if !seen_epon then
                      forward_inductives := fwd_ref :: !forward_inductives )
                  fwd_ind.ind_packets
              | _ -> () )
            sel;
          let excluded_refs = !module_type_aliases @ !forward_inductives in
          let rec refs_excluded ty =
            match ty with
            | Miniml.Tglob (r, args, _) ->
              List.exists
                (globref_equal r)
                excluded_refs
              || List.exists refs_excluded args
            | Miniml.Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
            | Miniml.Tmeta {contents = Some t} -> refs_excluded t
            | _ -> false
          in
          let process_decl (_l, se) =
            match se with
            | SEdecl d ->
              List.iter
                (fun {fd_ref = r; fd_body = body; fd_type = ty} ->
                  if same_module r && not (refs_excluded ty) then
                    Option.iter
                      (fun c -> method_candidates := c :: !method_candidates)
                      (planned_method_candidate epon_ref r body ty) )
                (Mlutil.term_defs d)
            | _ -> ()
          in
          List.iter process_decl sel;
          List.iter process_decl !current_structure_decls
        | Some _ | None -> () );
        let this_eponymous_record = !eponymous_record in
        let module_name_str_raw = Common.pp_module mp in
        let has_concept_collision =
          List.exists
            (fun (_l, se) ->
              match se with
              | SEdecl (Dind (kn, ind)) ->
                List.exists
                  (fun i ->
                    match ind.ind_kind with
                    | TypeClass _ ->
                      let ind_ref = GlobRef.IndRef (kn, i) in
                      String.equal
                        (Cpp_names.concept_name_of_ref ind_ref)
                        module_name_str_raw
                    | _ -> false )
                  (List.init (Array.length ind.ind_packets) Fun.id)
              | _ -> false )
            sel
        in
        let typeclass_concepts =
          if is_header then
            List.concat_map
              (fun (l, se) ->
                match se with
                | SEdecl (Dind (kn, ind)) ->
                  List.concat
                    (List.init (Array.length ind.ind_packets) (fun i ->
                       match ind.ind_kind with
                       | TypeClass fields ->
                         let ind_ref = GlobRef.IndRef (kn, i) in
                         let concept_pp, mentions_outer =
                           watching_for_reference_to
                             (Pp.string_of_ppcmds name)
                           @@ fun () ->
                           render_decl
                             (empty_env ())
                             (generated_concept ind_ref fields)
                         in
                         let doc = pp_doc_comment l in
                         [(HCclass ind_ref, doc ++ concept_pp, mentions_outer)]
                       | _ -> [] ) )
                (* A singleton class is declared as its method's type, and
                   becomes a concept all the same. *)
                | SEdecl (Dtype (r, _, _)) when Table.singleton_class_method r <> None ->
                  let concept_pp, mentions_outer =
                    watching_for_reference_to (Pp.string_of_ppcmds name) @@ fun () ->
                    render_decl (empty_env ())
                      (generated_concept r (Table.get_record_field_bindings r))
                  in
                  [(HCclass r, pp_doc_comment l ++ concept_pp, mentions_outer)]
                | _ -> [] )
              sel
          else
            []
        in
        (* A concept cannot be declared inside a struct, so the concepts of a
           module nested in another module travel to file scope instead of
           preceding their own struct. *)
        let typeclass_concepts =
          if old_context then (
            push_all file_scope_concepts
              (List.map (fun (_, c, _) -> c) typeclass_concepts);
            [] )
          else typeclass_concepts
        in
        (* A concept whose [requires] clause names one of the enclosing
           struct's own types cannot be emitted before that struct, whether it
           came from a module type or from a type class. *)
        let hold_back_after concepts =
          List.partition (fun (_, _, mentions_outer) -> not mentions_outer)
            concepts
        in
        let typeclass_concepts, typeclass_concepts_after =
          hold_back_after typeclass_concepts
        in
        let typeclasses_pp =
          if typeclass_concepts = [] then
            mt ()
          else
            fnl ()
            ++ prlist_with_sep fnl (fun (_, c, _) -> c) typeclass_concepts
            ++ fnl ()
            ++ fnl ()
        in
        let modtype_concepts =
          if is_header then
            List.filter_map
              (fun (l, se) ->
                match se with
                | SEmodtype m ->
                  let modtype_name = str (modtype_concept_name (MPdot (mp, l))) in
                  let concept_pp, mentions_outer =
                    watching_for_reference_to (Pp.string_of_ppcmds name)
                    @@ fun () -> pp_modtype_concept modtype_name m
                  in
                  Some (HCmodtype (MPdot (mp, l)), concept_pp, mentions_outer)
                | _ -> None )
              sel
          else
            []
        in
        (* Such a concept is held back and emitted after the struct instead;
           the others keep their place, since the struct's body may constrain
           a functor with them. *)
        let modtype_concepts, modtype_concepts_after =
          hold_back_after modtype_concepts
        in
        let this_held_back =
          List.map (fun (key, _, _) -> key)
            (typeclass_concepts_after @ modtype_concepts_after)
        in
        let concepts_group_pp concepts =
          if concepts = [] then
            mt ()
          else
            prlist_with_sep fnl (fun (_, c, _) -> c) concepts ++ fnl () ++ fnl ()
        in
        (* A concept cannot be declared inside a struct, so a module type
           belonging to a module that is itself nested travels to file scope,
           just as a typeclass concept does. *)
        let modtype_concepts, modtype_concepts_after =
          if old_context then (
            push_all file_scope_concepts
              (List.map (fun (_, c, _) -> c)
                 (modtype_concepts @ modtype_concepts_after));
            ([], []) )
          else (modtype_concepts, modtype_concepts_after)
        in
        let modtypes_pp = concepts_group_pp modtype_concepts in
        let concepts_after = typeclass_concepts_after @ modtype_concepts_after in
        let modtypes_after_pp =
          if concepts_after = [] then
            mt ()
          else
            fnl () ++ fnl () ++ concepts_group_pp concepts_after
        in
        (* Determine if this module should be promoted: eponymous inductive
           (not record) where the module struct IS the type directly. *)
        (* Only promote top-level modules (not nested inside another struct)
           that don't contain nested submodules with their own inductives.
           Promoting modules with nested types would break external
           accessibility of those types. *)
        let has_nested_submodules =
          List.exists
            (fun (_l, se) ->
              match se with
              | SEmodule _ -> true
              | _ -> false )
            sel
        in
        let has_extra_inductives =
          let ind_count =
            List.fold_left
              (fun acc (_l, se) ->
                match se with
                | SEdecl (Dind _) -> acc + 1
                | _ -> acc )
              0
              sel
          in
          ind_count > 1
        in
        let is_promoted =
          !eponymous_type_ref <> None
          && (not old_context)
          && (not has_nested_submodules)
          && not has_extra_inductives
        in
        (* Extract template params from the eponymous inductive packet. *)
        let promoted_tparams =
          if is_promoted then
            List.find_map
              (fun (_l, se) ->
                match se with
                | SEdecl (Dind (kn, ind)) ->
                  let found = ref None in
                  Array.iteri
                    (fun i p ->
                      let ind_ref = GlobRef.IndRef (kn, i) in
                      if
                        Option.map
                          (fun r ->
                            globref_equal r ind_ref )
                          !eponymous_type_ref
                        = Some true
                      then
                        let (param_vars, _) = Table.ind_param_vars ind p in
                        (* The promoted variables the payloads name are
                           parameters too -- see {!Table.ind_promoted_params}
                           and its use in [Cpp_ind]; the head spelled here must
                           be the one the struct is generated with. *)
                        found :=
                          Some (Table.ind_promoted_params kn @ param_vars) )
                    ind.ind_packets;
                  !found
                | _ -> None )
              sel
          else
            None
        in
        (* Set the promotion state the body will be rendered under.  A
           promotion outlives this module -- every later mention of the
           inductive spells it the promoted way -- whereas the demotion a
           nested rendering needs lasts exactly as long as that rendering. *)
        let with_promotion_scope =
          if is_promoted then (
            eponymous_promote_ref := !eponymous_type_ref;
            Option.iter Table.promote_inductive !eponymous_type_ref;
            eponymous_deferred := Pp.mt ();
            eponymous_promote_sft := false;
            fun body -> body () )
          else
            Table.with_demoted_inductive !eponymous_type_ref
        in
        (* Where the body of this module is rendered: inside the struct when
           the header spells it out, qualified by it in the implementation. *)
        let enter_module c =
          let c =
            if has_concept_collision then c
            else if is_header then
              (* For promoted modules with template params, set rc_in_template
                 so non-inductive defs inside get full inline definitions. *)
              let promoted_template =
                is_promoted
                && match promoted_tparams with Some (_ :: _) -> true | _ -> false
              in
              { c with
                rc_in_struct = true;
                rc_in_template = c.rc_in_template || promoted_template }
            else
              { c with
                rc_struct_name =
                  ( match c.rc_struct_name with
                  | Some parent -> Some (parent ++ str "::" ++ name)
                  | None -> Some name );
                rc_struct_mp = Some mp }
          in
          if is_header && typeclass_concepts <> [] then
            { c with rc_concepts_hoisted = true }
          else c
        in
        let body, deferred_asserts_pp, this_method_candidates =
          with_promotion_scope @@ fun () ->
          with_render_ctx enter_module (fun () ->
            let held, (body, candidates) =
              collecting deferred_concept_asserts (fun () ->
                  let body =
                    setting
                      held_back_concepts
                      (this_held_back @ !held_back_concepts)
                      (fun () -> pp_module_expr ~is_header f [] m.ml_mod_expr)
                  in
                  (body, !method_candidates) )
            in
            (* The assertions this struct held back: those naming a concept it
               declares are emitted after it, now that both are in scope; the rest
               travel further out, qualified by this struct on the way. *)
            let mine, passed_out =
              List.partition
                (fun (mt_mp, _, _) -> is_held_back_in this_held_back mt_mp)
                held
            in
            let deferred_asserts_pp =
              prlist
                (fun (_, concept, sub) ->
                  pp_concept_assert concept (name ++ str "::" ++ sub) )
                mine
            in
            deferred_concept_asserts :=
              List.rev_append
                (List.map
                   (fun (mt_mp, concept, sub) ->
                     (mt_mp, concept, name ++ str "::" ++ sub) )
                   passed_out )
                !deferred_concept_asserts;
            (body, deferred_asserts_pp, candidates) )
        in
        (* Capture and clean up promotion state. *)
        let this_promoted = is_promoted in
        let this_deferred = !eponymous_deferred in
        let this_promote_sft = !eponymous_promote_sft in
        if is_promoted then (
          eponymous_promote_ref := None;
          eponymous_deferred := Pp.mt ();
          eponymous_promote_sft := false );
        if is_header then
          if this_promoted then
            (* Promoted module: the module struct IS the eponymous type. Wrap
               body in a template struct with the inductive's template params
               and emit deferred defs at file scope. *)
            let template_decl =
              match promoted_tparams with
              | Some (_ :: _ as vars) ->
                str "template<"
                ++ prlist_with_sep
                     (fun () -> str ", ")
                     (fun v ->
                       str "typename " ++ Id.print (Common.tparam_name v) )
                     vars
                ++ str ">"
                ++ fnl ()
              | _ -> mt ()
            in
            let inherit_clause =
              if this_promote_sft then
                let type_args =
                  match promoted_tparams with
                  | Some (_ :: _ as vars) ->
                    str "<"
                    ++ prlist_with_sep
                         (fun () -> str ", ")
                         (fun v -> Id.print (Common.tparam_name v))
                         vars
                    ++ str ">"
                  | _ -> mt ()
                in
                str " : public " ++ str (sn ()).enable_from_this ++ str "<"
                ++ name
                ++ type_args
                ++ str ">"
              else
                mt ()
            in
            let struct_def =
              template_decl
              ++ str "struct "
              ++ name
              ++ inherit_clause
              ++ str " {"
              ++ fnl ()
              ++ body
              ++ str "};"
            in
            typeclasses_pp ++ modtypes_pp ++ struct_def ++ modtypes_after_pp
            ++ deferred_asserts_pp
            ++ this_deferred
          else
            let template_decl, record_fields_pp, record_methods_pp =
              match this_eponymous_record with
              | Some (epon_ref, fields, packet) ->
                let ty_vars = packet.ip_vars in
                let template_str =
                  if ty_vars = [] then
                    mt ()
                  else
                    str "template<"
                    ++ prlist_with_sep
                         (fun () -> str ", ")
                         (fun v -> str "typename " ++ Id.print v)
                         ty_vars
                    ++ str ">"
                    ++ fnl ()
                in
                (* [fields] already pairs each projection with its type:
                   extraction selected the two together. *)
                let field_list = fields in
                let pp_field i (field_ref, field_ty) =
                  let field_name =
                    match field_ref with
                    | Some r -> str (Common.pp_global_name Term r)
                    (* Index anonymous fields so multiple of them don't all
                       collapse to a single duplicate "_field" member (which
                       would not compile).  Matches gen_decls.ml. *)
                    | None -> str ("_field" ^ string_of_int i)
                  in
                  let cpp_ty =
                    pp_cpp_type
                      false
                      ty_vars
                      (convert_ml_type_to_cpp_type
                         (empty_env ())
                         ty_vars
                         field_ty )
                  in
                  cpp_ty ++ spc () ++ field_name ++ str ";"
                in
                let fields_pp =
                  prlist_with_sep fnl (fun p -> p) (List.mapi pp_field field_list)
                  ++ fnl ()
                in
                let non_projection_candidates =
                  List.filter
                    (fun (r, _, _, _) -> not (Table.is_projection r))
                    (List.rev this_method_candidates)
                in
                let method_fields, method_helpers =
                  generated_record_methods epon_ref ty_vars non_projection_candidates
                in
                (* A struct is a complete-class context, so a helper lifted out
                   of a method is a member that may follow the methods calling
                   it; it precedes them here. *)
                let helpers_pp =
                  prlist
                    (fun h ->
                      pp_cpp_decl (empty_env ()) (fst (lifted_views ~may_hoist:false h))
                      ++ fnl () )
                    (dedup_lifted_decls method_helpers)
                in
                let methods_pp =
                  if method_fields = [] then
                    mt ()
                  else
                    (* The record's methods are members of the module struct
                       it was merged into, and pass through every stage a
                       member does -- loopification, moves, the constraints
                       their bodies settle -- before they are printed. *)
                    let finished =
                      Cpp_pipeline.finish
                        (Dfields
                           { ds_ref = epon_ref;
                             ds_fields = method_fields;
                             ds_tparams =
                               List.map (fun v -> (TTtypename, v)) ty_vars;
                             ds_constraint = None;
                             ds_needs_shared_from_this = false } )
                    in
                    let fields =
                      match (finished :> cpp_decl) with
                      | Dfields ds -> ds.ds_fields
                      | _ -> method_fields
                    in
                    setting method_candidates this_method_candidates (fun () ->
                        helpers_pp
                        ++ prlist_with_sep
                             fnl
                             (fun (fld, _vis, _tag) -> pp_cpp_field (empty_env ()) fld)
                             fields
                        ++ fnl () )
                in
                (template_str, fields_pp, methods_pp)
              | None -> (mt (), mt (), mt ())
            in
            if has_concept_collision then
              typeclasses_pp
              ++ modtypes_pp
              ++ record_fields_pp
              ++ record_methods_pp
              ++ body
            else if Pp.ismt body && Pp.ismt record_fields_pp
                    && Pp.ismt record_methods_pp then
              (* Empty module: emit [struct Name {};] even though there are
                 no declarations.  The struct may be needed as a template
                 argument in functor instantiations, e.g.
                 [using M_ = M<Empty>;] where [Empty] was defined as an
                 empty Rocq module satisfying some module type.  Previously
                 this returned [mt ()] which suppressed the struct
                 entirely, causing undeclared-identifier errors. *)
              template_decl ++ str "struct " ++ name ++ str " {};"
            else
              let struct_def =
                template_decl
                ++ str "struct "
                ++ name
                ++ str " {"
                ++ fnl ()
                ++ record_fields_pp
                ++ record_methods_pp
                ++ body
                ++ str "};"
              in
              typeclasses_pp ++ modtypes_pp ++ struct_def ++ modtypes_after_pp
              ++ deferred_asserts_pp
              ++ concept_assert_pp name m.ml_mod_type
        else if this_promoted then
          (* Promoted template: all defs are inline in header, skip .cpp *)
          mt ()
        else
          body
      | MEident target ->
        if not is_header then
          mt ()
        else
          (* The target is a module path, so it resolves to a name that says
             for itself whether it came out qualified. *)
          let resolved = Common.resolve_module target in
          let body = str (Common.resolved_string resolved) in
          (* Check whether this alias is itself a functor (i.e., the module
             type has MTfunsig parameters).  This happens when Rocq's
             extraction eta-reduces [Module Facts (M:WS) := WFacts M.] to
             [MEident(WFacts)].  A bare [using Facts = WFacts;] is invalid
             C++ when WFacts is a template struct; we need a template alias
             [template<WS M> using Facts = WFacts<M>;] instead. *)
          let rec collect_functor_params acc = function
            | MTfunsig (mbid, mt, rest) ->
              collect_functor_params ((mbid, mt) :: acc) rest
            | _ -> List.rev acc
          in
          let functor_params = collect_functor_params [] m.ml_mod_type in
          if functor_params = [] then
            (* Non-functor alias. File-level modules are rendered as C++
               namespaces; a [using R = Namespace;] alias inside a struct
               body is invalid C++, so we drop it.  Aliases whose target is
               a sub-module (MPdot — rendered as a struct) are valid type
               aliases inside a struct body and are kept. *)
            let target_is_namespace =
              match m.ml_mod_expr with
              | MEident mp -> is_modfile mp
              | _ -> false
            in
            if target_is_namespace && (!render_ctx).rc_in_struct then
              mt ()
            else
              let body_with_typename =
                if
                  (!render_ctx).rc_in_template
                  && Common.resolved_is_qualified resolved
                then
                  str "typename " ++ body
                else body
              in
              str "using " ++ name ++ str " = " ++ body_with_typename ++ str ";"
          else begin
            (* Functor alias: emit [template<...> using Name = Body<params>;].
               Re-uses {!pp_template_param} from the MEfunctor case. *)
            let template_decl =
              str "template<"
              ++ prlist_with_sep
                   (fun () -> str ", ")
                   pp_template_param
                   functor_params
              ++ str ">"
            in
            let param_args =
              prlist_with_sep
                (fun () -> str ", ")
                (fun (mbid, _) -> pp_modname (MPbound mbid))
                functor_params
            in
            template_decl
            ++ fnl ()
            ++ str "using "
            ++ name
            ++ str " = "
            ++ body
            ++ str "<"
            ++ param_args
            ++ str ">;"
          end
    in
    if Pp.ismt mod_pp then
      mt ()
    else
      let doc = pp_doc_comment l in
      let whole = doc ++ mod_pp in
      (* A [Module] of nothing but definitions is rendered as a struct of
         declarations, and a datatype's hoisted member may call one; see
         {!module_struct_is_hoistable}. *)
      if
        is_header
        && (not (!render_ctx).rc_in_struct)
        && (match m.ml_mod_expr with
           | MEstruct (_, sel) -> module_members_name_only_inductives sel
           | _ -> false)
        && module_struct_is_hoistable (Pp.string_of_ppcmds whole)
      then (
        hoisted_module_structs := whole :: !hoisted_module_structs;
        mt () )
      else whole
  | l, SEmodtype m ->
    if (not is_header) || (!render_ctx).rc_in_struct then
      mt ()
    else
      pp_modtype_concept (str (modtype_concept_name (MPdot (top_visible_mp (), l)))) m

(** Render a functor application, and say whether the result comes out with a
    [::] qualifier.

    Qualification is a property of the name at the application's head, not of
    the whole rendering: [F<A::B>] needs no [typename], [A::F<B>] does.  The
    question used to be put to the rendered text, which cannot tell those two
    apart.  Returning the head's resolution alongside the document lets a
    nested application answer for itself, and resolves each name exactly once.

    The head is never itself an application -- the argument collection below
    flattens those -- and a struct or functor abstraction has no name to
    qualify, hence the [None]. *)
and pp_module_app ~is_header f me me' =
  let rec collect_args acc = function
    | MEapply (g, arg) -> collect_args (arg :: acc) g
    | base -> (base, acc)
  in
  let base, args = collect_args [me'] me in
  let render me =
    match me with
    | MEident mp ->
      let r = Common.resolve_module mp in
      (str (wrapper_qualify_modname mp (Common.resolved_string r)), Some r)
    | MEapply (g, g') -> pp_module_app ~is_header f g g'
    | _ -> (pp_module_expr ~is_header f [] me, None)
  in
  let is_qualified = function
    | Some r -> Common.resolved_is_qualified r
    | None -> false
  in
  let base_pp, base_resolved = render base in
  let pp_module_arg arg =
    let arg_pp, arg_resolved = render arg in
    if (!render_ctx).rc_in_template && is_qualified arg_resolved then
      str "typename " ++ arg_pp
    else arg_pp
  in
  let args_pp = prlist_with_sep (fun () -> str ", ") pp_module_arg args in
  let head_pp =
    if (!render_ctx).rc_in_template && is_qualified base_resolved then
      (* [A::B<...>] must be spelled [A::template B<...>] inside a template. *)
      match
        match base_resolved with
        | Some r -> Common.resolved_split r
        | None -> None
      with
      | Some (qual, last) -> str qual ++ str "::template " ++ str last
      | None -> base_pp
    else base_pp
  in
  (head_pp ++ str "<" ++ args_pp ++ str ">", base_resolved)

(** Pretty-print a module expression (MEident, MEapply, MEfunctor, MEstruct).

    @param is_header  Controls header vs. implementation rendering (see
                      {!pp_structure_elem}).
    @param f          Callback for rendering individual declarations inside an
                      [MEstruct] body.
    @param params     Bound module paths accumulated from enclosing [MEfunctor]
                      binders; pushed onto the visibility stack when the
                      [MEstruct] body is entered.
    @return Pretty-printer document for the module expression. For [MEident]
            this is the qualified module name; for [MEapply] a template
            instantiation; for [MEstruct] the indented body of declarations. *)
and pp_module_expr ~is_header f params = function
  | MEident mp -> pp_modname mp
  | MEapply (me, me') -> fst (pp_module_app ~is_header f me me')
  | MEfunctor (mbid, mt, me) ->
    pp_module_expr ~is_header f (MPbound mbid :: params) me
  | MEstruct (mp, sel) ->
    push_visible mp params;
    add_visible_members (member_names_of_sel sel);
    let old_structure_decls = !current_structure_decls in
    current_structure_decls := sel;
    let old_local_inductives = get_local_inductives () in
    List.iter
      (fun (_l, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          let ind_mp = Names.MutInd.modpath kn in
          if (not (modular ())) || Names.ModPath.equal ind_mp mp then
            Array.iteri
              (fun i _p -> add_local_inductive (GlobRef.IndRef (kn, i)))
              ind.ind_packets
        | _ -> () )
      sel;
    (* A synthesised alias whose body names this module's own types, as its
       members spell them, is declared inside the struct, in front of the
       first member that spells it (see {!Cpp_print.record_ctor_alias_home}):
       at namespace scope those names mean nothing. *)
    let with_homed_aliases px =
      match Cpp_print.pending_ctor_aliases_homed_in mp with
      | [] -> px
      | homed ->
        let text = Pp.string_of_ppcmds px in
        let select name =
          List.mem name homed && Cpp_print.mentions_name text name
        in
        if not (List.exists select homed) then px
        else
          match Cpp_print.take_ctor_alias_decls ~select ~is_header () with
          | [] -> px
          | l -> prlist_with_sep fnl (fun x -> x) l ++ cut2 () ++ px
    in
    let try_pp_structure_elem l x =
      let px = pp_structure_elem ~is_header f x in
      if Pp.ismt px then l else with_homed_aliases px :: l
    in
    let l = List.fold_left try_pp_structure_elem [] sel in
    let l = List.rev l in
    clear_local_inductives ();
    List.iter add_local_inductive old_local_inductives;
    current_structure_decls := old_structure_decls;
    pop_visible ();
    if List.is_empty l then
      mt ()
    else
      (prlist_with_doc_safe_sep cut2 l) ++ fnl ()

(** Like [prlist_with_sep] but skips empty ([mt ()]) elements.

    @param sep  Thunk producing the separator document inserted between
                consecutive non-empty rendered elements.
    @param f    Function applied to each list element to produce its document.
    @return Concatenation of all non-empty documents separated by [sep ()],
            or [mt ()] if every element renders empty. *)
let rec prlist_sep_nonempty sep f = function
  | [] -> mt ()
  | [h] -> f h
  | h :: t ->
    let e = f h in
    let r = prlist_sep_nonempty sep f t in
    if Pp.ismt e then
      r
    else if Pp.ismt r then
      e
    else
      let boundary = if starts_with_doc_comment r then fnl () else sep () in
      e ++ boundary ++ r

(** The declarations and definitions generated functions contribute to the
    file being written, grouped as [gens] is: each one's declaration always,
    its definition only in the file that holds it.

    Every definition is finished before it is split, and all of them as one
    group ({!Function_entity.finalize_group}): a wrapper's functions may call
    one another in any order. *)
let file_views ~is_header (gens : Gen_decls.generated_fun list list) =
  let views ((g : Gen_decls.generated_fun), entity) =
    let with_env d = (d, g.gf_env) in
    match (g.gf_entity, entity) with
    | Defined (_, file), Some e ->
      ( [with_env (Function_entity.declaration e)],
        if (file = Gen_decls.Header) = is_header then
          [with_env (Function_entity.definition_after_declaration e)]
        else [] )
    | Declared d, _ -> ([with_env (Cpp_pipeline.finish d)], [])
    | Defined _, None -> assert false
  in
  let rec regroup gens views =
    match gens with
    | [] -> []
    | gs :: gens ->
      let mine, rest = List.chop (List.length gs) views in
      (List.concat_map fst mine, List.concat_map snd mine) :: regroup gens rest
  in
  regroup gens (List.map views (Cpp_ind.finalized (List.concat gens)))

(** Process a wrapper module in dual-pass mode (header vs implementation).

    PASS 1 (is_header=true): Emit forward declarations (specs) for functions.
    PASS 2 (is_header=false): Emit full definitions (defs) for functions.

    Each function is generated once, independent of the file; [is_header]
    only picks which of its views this file writes ({!file_views}).

    @param is_header   When [true] produce declaration specs; when [false]
                       produce out-of-line definitions.
    @param wrapper_mp  The module path of the wrapper module being rendered;
                       used to set [rc_struct_mp] so that out-of-line
                       definitions are correctly qualified.
    @param wrapper_name  The C++ struct name of the wrapper (e.g. ["Facts"]);
                         used to set [rc_struct_name] in the definition pass.
    @param func_sels   The [(label, structure_elem)] pairs from the wrapper
                       that contain function declarations ([Dterm], [Dfix]).
    @return A quadruple [(specs_pp, defs_pp, lifted_pp, lifted_specs_pp)] where
            [specs_pp] is the header-pass declaration block, [defs_pp] the
            implementation-pass definition block, [lifted_pp] any top-level
            declarations that were lifted out of local function bodies during
            translation, and [lifted_specs_pp] the forward declarations of the
            functions among those, which are due before the struct rather than
            after it. *)
let pp_wrapper_module_dual ~is_header ~wrapper_mp wrapper_name func_sels =
  let is_method_candidate x =
    List.exists
      (fun (r', _, _, _) -> globref_equal x r')
      !method_candidates
  in
  let process_sel (_l, se) =
    match se with
    | SEdecl (Dterm (r, _, _)) when is_any_inline_custom r -> ([], [])
    | SEdecl (Dterm (r, _, _)) when is_eponymous_record_projection r ->
      ([], [])
    | SEdecl (Dterm (r, _, _)) when is_suppressed_projection r -> ([], [])
    | SEdecl (Dterm (r, _, _)) when is_method_candidate r -> ([], [])
    (* A function registered as a method of another module's type is
       generated with that type. *)
    | SEdecl (Dterm (r, _, _)) when is_registered_method r <> None -> ([], [])
    | SEdecl (Dterm (r, _a, Tglob (ty, _args, _e))) when is_monad ty ->
      ([], [])
    (* An instance is a struct, and it is named from wherever its class is
       used -- unqualified, because a concept's template argument is a type,
       not a member of whatever module happened to declare it.  So it is
       lifted out of the wrapper's struct to namespace scope, exactly as an
       instance declared at the extraction root is emitted.  Dropping it here
       left every use of it undeclared. *)
    | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t ->
      (* The helpers lifted out of its methods come first: the instance
         struct calls them. *)
      let ds, helpers = generated_entity r (fun () -> instance_decls r a t) in
      ([], helpers @ List.map snd ds)
    | SEdecl (Dterm (r, a, t)) ->
      let gs = generated_once se (fun () -> [gen_decl_for_pp_dual r a t]) in
      record_funs ~fallback:r gs;
      let lifted = List.concat_map (fun g -> g.gf_lifted) gs in
      List.iter (dbg_lifted ~site:"wrapper-dterm") lifted;
      (gs, lifted)
    | SEdecl (Dfix fds) -> (
      match filter_dfix fds with
      | [] -> ([], [])
      | ({fd_ref; _} :: _) as fds ->
        let results = generated_once se (fun () -> gen_dfuns_dual fds) in
        record_funs ~fallback:fd_ref results;
        (results, List.concat_map (fun g -> g.gf_lifted) results) )
    | _ -> ([], [])
  in
  let generated = List.map process_sel func_sels in
  let all_results = file_views ~is_header (List.map fst generated) in
  let all_lifted =
    List.concat_map snd generated
    |> dedup_lifted_decls in
  let render_sel_specs (specs, _) =
    match specs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) specs
  in
  let render_sel_defs (_, defs) =
    match defs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) defs
  in
  let specs_pp =
    with_render_ctx
      (fun c -> { c with rc_in_struct = true })
      (fun () -> prlist_sep_nonempty cut2 render_sel_specs all_results)
  in
  let defs_pp =
    with_render_ctx
      (fun c ->
        { c with
          rc_struct_name = Some (str wrapper_name);
          rc_struct_mp = Some wrapper_mp } )
      (fun () -> prlist_sep_nonempty cut2 render_sel_defs all_results)
  in
  (* A lifted helper is emitted after the struct it was lifted out of, and its
     callers are inside that struct, so by the time the definition appears the
     name has already been used.  A wrapper struct's own members do not have
     this problem -- {!gen_dfuns_dual} declares them all before defining any --
     and this is the same repair for the one kind of function that path never
     reaches, because it is not a member.  Only functions: a lifted struct is
     already forward-declared where structs are, and a declaration of anything
     else is either illegal or a second definition.

     Both halves come out of one split so they state one template head, and the
     definition emitted here is the split's, not the one that went in.  Only
     the header writes either. *)
  let lifted_split =
    if is_header then List.map lifted_views all_lifted else []
  in
  let lifted_pp =
    prlist_sep_nonempty cut2
      (fun (def, _) -> pp_cpp_decl (empty_env ()) def)
      lifted_split
  in
  let lifted_specs_pp =
    prlist_sep_nonempty cut2
      (pp_cpp_decl (empty_env ()))
      (List.filter_map snd lifted_split)
  in
  (specs_pp, defs_pp, lifted_pp, lifted_specs_pp)

(** What analysing the structure concluded, for the passes that render it. *)
let structure_analysis : Structure_analysis.t option ref = ref None

(** The analysis of the structure being rendered.

    Absent means a pass was started without {!prepare_structure}, which is a
    bug in the caller rather than a structure with nothing to say. *)
let get_structure_analysis () =
  match !structure_analysis with
  | Some a -> a
  | None ->
    CErrors.anomaly (Pp.str "cpp: rendering a structure that was never analysed")

(** The module plan a structure analysis decides, with the functor concept
    scopes, which rendering reads from here, installed.

    Every field of {!Structure_analysis.t} but [sorted_modules] exists to be
    read while rendering, so they are all taken here: rendering only ever
    reads what they decide, and so cannot render a use before the decision it
    depends on has been made.  The record is destructured field by field under
    warning 9, which is what makes a field added to the analysis and not
    handled here a compile error rather than a decision nothing acts on. *)
let module_plan_of_analysis
    ({ sorted_modules;
       global_scope_enums;
       collision_wrappers;
       wrapper_bystanders;
       functor_app_sources;
       eponymous_records;
       functor_concept_scopes = scopes;
       concept_renames;
       modtype_concept_renames;
       lifted_instances;
       _ } :
      Structure_analysis.t ) : Module_plan.t =
  functor_concept_scopes := scopes;
  let wrapped =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) ->
        Option.map (fun name -> (mi, name)) mi.wrapper_name )
      sorted_modules
  in
  { global_scope_enums;
      concept_names = concept_renames;
      modtype_concept_names = modtype_concept_renames;
      functor_app_sources;
      eponymous_records;
      namespace_scope_refs = lifted_instances;
      wrappers =
        List.map (fun (mp, name) -> (mp, name, Some Module_plan.Flattened)) collision_wrappers
        (* A bystander is nested inside the wrapper, not flattened into it. *)
        @ List.map (fun (mp, name) -> (mp, name, Some Module_plan.Bystander)) wrapper_bystanders
        @ List.map (fun ((mi : Structure_analysis.module_info), name) -> (mi.modpath, name, None)) wrapped;
      (* Not everything a wrapper module declares ends up inside the wrapper
         struct.  A type alias is emitted at global C++ scope as
         [using T = ...;], and a type class instance is lifted out to namespace
         scope by [process_sel] below, for the reason recorded there.  Either
         way {!Cpp_names.struct_qualifier_for} must not write [Wrapper::] in
         front of the name in the .cpp file.  Which module a declaration is
         emitted in is layout, so it is settled here rather than while
         emitting it. *)
      global_scope_types =
        List.concat_map
          (fun ((mi : Structure_analysis.module_info), _) ->
            List.filter_map
              (fun (_l, se) ->
                match se with
                | SEdecl (Dtype (r, _, _)) -> Some r
                | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t -> Some r
                | _ -> None )
              mi.sels )
          wrapped }

(** Decide everything about the structure that does not depend on which file is
    being written, record what rendering reads of it here, and return its
    {!Module_plan} -- the layout -- for the target plan to hold.

    {!Structure_analysis} describes itself as running before rendering, and the
    tables it fills are read by both the header and the implementation; it was
    nonetheless invoked from inside the renderer, so the same conclusions were
    reached four times per unit and the last one silently won.  Reaching them
    once, here, is what makes discovery a pass in its own right.

    The visibility stack is pushed exactly as a rendering pass would push it:
    the analysis is a function of the structure, but the helpers it calls read
    the stack, and this is a relocation, not a re-derivation. *)
let prepare_structure s =
  let initial_mps =
    List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s
  in
  List.iter (fun mp -> push_visible mp []) initial_mps;
  Common.detect_sibling_module_inductive_collisions s;
  method_registry :=
    Some
      ( match !global_method_registry with
      | Some reg -> reg
      | None ->
        Method_registry.create
          ~ret_is_erased:Translation.return_type_is_erased s );
  let analysis = Structure_analysis.analyze (get_method_registry ()) s in
  let modules = module_plan_of_analysis analysis in
  (* Whether an inductive is a flat struct is a property of its declaration;
     every reader, before or after its struct is generated, gets one answer. *)
  Modutil.struct_iter
    (function
      | Dind (kn, ind) ->
        Array.iteri
          (fun i _ ->
            let r = GlobRef.IndRef (kn, i) in
            if Table.is_flat_inductive_packet kn ind i then
              Table.add_flat_inductive r )
          ind.ind_packets
      | _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    s;
  List.iter (fun _ -> pop_visible ()) initial_mps;
  structure_analysis := Some analysis;
  modules

(** The callable plan of each function the renders will generate, in the
    order of the unit's modules and declarations, or the reverse if
    [reversed]: planned before anything is rendered
    ({!Gen_decls.plan_function}), so that a call rendered ahead of its callee
    reads the head the callee is declared with.

    The modules are walked as a render walks them, for the two things a head
    is converted against: the visibility stack, and the inductives local to
    the enclosing modules.  Only what a render generates as a function is
    planned: a method, a projection, an inline custom and an alias's copy are
    not, and neither is a wrapper module's monadic constant, which no render
    generates at all.  Planning one of those would hand its call sites a head
    other than the one they assume; missing one is reported when it is
    generated ({!Callable_abi.check}).

    A method is planned where its inductive is declared, for each function
    registered as one ({!Gen_decls.plan_method}): at the variables of an
    eponymous record's own declaration, which its methods are generated
    with, and otherwise at those of the inductive's struct. *)
let plan_callables ?(reversed = false) s =
  let order l = if reversed then List.rev l else l in
  let analysis = get_structure_analysis () in
  let plans = ref [] in
  let plan ~fixpoint r a t =
    if not (is_any_inline_custom r || Table.is_projection r || is_registered_method r <> None)
    then Option.iter (fun abi -> plans := abi :: !plans) (Gen_decls.plan_function ~fixpoint r a t)
  in
  let plan_methods kn ind =
    Array.iteri
      (fun i p ->
        let ind_ref = GlobRef.IndRef (kn, i) in
        if not (is_custom ind_ref || is_monad ind_ref) then
          let vars =
            if List.exists (globref_equal ind_ref) analysis.eponymous_records then p.ip_vars
            else Common.ind_struct_tparams kn ind p
          in
          List.iter
            (fun ((r, _, _, _) as candidate) ->
              if not (Table.is_projection r) then
                plans := Gen_decls.plan_method ind_ref vars candidate :: !plans )
            (order (Method_registry.get_candidates (get_method_registry ()) ind_ref)) )
      ind.ind_packets
  in
  (* A monadic constant is generated as a recursive group of one. *)
  let plan_decl ~wrapper = function
    | Dterm (r, a, (Tglob (ty, _, _) as t)) when is_monad ty ->
      if not wrapper then plan ~fixpoint:true r a t
    | Dterm (r, a, t) when not (is_typeclass_instance a t) -> plan ~fixpoint:false r a t
    | Dfix fds ->
      List.iter (fun fd -> plan ~fixpoint:true fd.fd_ref fd.fd_body fd.fd_type) (order fds)
    | Dind (kn, ind) -> plan_methods kn ind
    | Dterm _ | Dtype _ -> ()
  in
  let declared_inductives mp sel =
    List.concat_map
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ind))
          when (not (modular ())) || ModPath.equal (MutInd.modpath kn) mp ->
          List.init (Array.length ind.ind_packets) (fun i -> GlobRef.IndRef (kn, i))
        | _ -> [] )
      sel
  in
  let in_module ?(params = []) mp k =
    push_visible mp params;
    Fun.protect ~finally:pop_visible k
  in
  let with_local_inductives refs k =
    let outer = get_local_inductives () in
    List.iter add_local_inductive refs;
    Fun.protect
      ~finally:(fun () ->
        clear_local_inductives ();
        List.iter add_local_inductive outer )
      k
  in
  let rec plan_elem ~wrapper (_, se) =
    match se with
    | SEdecl d -> plan_decl ~wrapper d
    | SEmodule {ml_mod_expr = MEfunctor _ as me; _} ->
      (* A functor is a class template, its parameters visible in its body. *)
      let rec split params = function
        | MEfunctor (mbid, _, me) -> split (params @ [MPbound mbid]) me
        | body -> (params, body)
      in
      let params, body = split [] me in
      with_render_ctx
        (fun c -> {c with rc_in_struct = true; rc_in_template = true})
        (fun () -> plan_module_expr ~params body)
    | SEmodule {ml_mod_expr; _} -> plan_module_expr ~params:[] ml_mod_expr
    | SEmodtype _ -> ()
  and plan_module_expr ~params = function
    | MEstruct (mp, sel) ->
      in_module ~params mp (fun () ->
          with_local_inductives (declared_inductives mp sel) (fun () ->
              List.iter (plan_elem ~wrapper:false) (order sel) ) )
    | MEident _ | MEapply _ | MEfunctor _ -> ()
  in
  let rec all_inductives sel =
    List.concat_map
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          List.init (Array.length ind.ind_packets) (fun i -> GlobRef.IndRef (kn, i))
        | SEmodule {ml_mod_expr = MEstruct (_, sub); _} -> all_inductives sub
        | _ -> [] )
      sel
  in
  let initial_mps = List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s in
  List.iter (fun mp -> push_visible mp []) initial_mps;
  Fun.protect
    ~finally:(fun () -> List.iter (fun _ -> pop_visible ()) initial_mps)
    (fun () ->
      (* A wrapper module's functions are generated before any inductive is
         made local. *)
      List.iter
        (fun (mi : Structure_analysis.module_info) ->
          if mi.wrapper_name <> None then
            in_module mi.modpath (fun () -> List.iter (plan_elem ~wrapper:true) (order mi.sels)) )
        (order analysis.sorted_modules);
      let file_inductives =
        if modular () then
          List.concat_map (fun (mi : Structure_analysis.module_info) -> all_inductives mi.sels) analysis.sorted_modules
        else []
      in
      with_local_inductives file_inductives (fun () ->
          List.iter
            (fun (mi : Structure_analysis.module_info) ->
              if mi.wrapper_name = None then
                in_module mi.modpath (fun () -> List.iter (plan_elem ~wrapper:false) (order mi.sels)) )
            (order analysis.sorted_modules) ) );
  List.rev !plans

let plan_names s =
  let names = ref [] in
  let name k r =
    if not (is_custom r || is_any_inline_custom r) then
      names := (r, Common.global_name k r) :: !names
  in
  let rec elems sel =
    List.iter
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          Array.iteri
            (fun i p ->
              name Type (GlobRef.IndRef (kn, i));
              Array.iteri (fun j _ -> name Cons (GlobRef.ConstructRef ((kn, i), j + 1))) p.ip_types )
            ind.ind_packets
        | SEdecl (Dtype (r, _, _)) -> name Type r
        | SEdecl (Dterm (r, _, _)) -> name Term r
        | SEdecl (Dfix fds) -> List.iter (fun fd -> name Term fd.fd_ref) fds
        | SEmodule {ml_mod_expr = MEstruct (_, sel); _} -> elems sel
        | SEmodule _ | SEmodtype _ -> () )
      sel
  in
  List.iter (fun (_, sel) -> elems sel) s;
  List.rev !names

(** [pp_wrapper_struct name specs] is the struct a library module is rendered
    as: its member declarations, [specs], inside a struct of that name. *)
let pp_wrapper_struct name specs =
  str "struct " ++ str name ++ str " {" ++ fnl () ++ specs ++ fnl () ++ str "};"

(** What rendering one wrapper module produced, beyond the declarations that
    merge into its struct.

    [wr_defs] are the out-of-line definitions, which follow the whole file.
    [wr_lifted] is a declaration lifted out of the module -- an instance struct,
    whose concept argument is a type no module owns -- and is due at the
    module's own place in the topological order, because a later module's
    constant may be initialised from it.

    A lifted declaration is emitted once: whoever emits it empties the field,
    so what is left at the end of the file is exactly what no module's turn
    came round to claim.

    [wr_lifted_specs] are the forward declarations of the functions among them,
    and go at the top of the file instead, because the callers of a lifted
    helper are inside the struct it was lifted out of and so precede it
    wherever its definition lands. *)
type wrapper_render = {
  wr_name : string;
  wr_defs : Pp.t;
  mutable wr_lifted : Pp.t option;
  wr_lifted_specs : Pp.t;
}

(** Declare, in front of [p], those synthesised aliases whose names [p] spells.

    Called on each chunk of the file in the order the chunks are written, so an
    alias is declared in front of the earliest text that uses it and nowhere
    else: the registry keeps what nothing has asked for yet.  Rendering [p] to
    a string is the whole test, and is skipped when there is nothing pending,
    so a file that mints no alias pays nothing. *)
let prefix_mentioned_aliases ~is_header p =
  let prefix l p =
    match l with
    | [] -> p
    | l when Pp.ismt p -> prlist_with_sep fnl (fun x -> x) l
    | l -> prlist_with_sep fnl (fun x -> x) l ++ cut2 () ++ p
  in
  let p =
    match Cpp_print.pending_ctor_alias_names () with
    | [] -> p
    | pending ->
      let text = Pp.string_of_ppcmds p in
      if not (List.exists (Cpp_print.mentions_name text) pending) then p
      else
        let select name = Cpp_print.mentions_name text name in
        prefix (Cpp_print.take_ctor_alias_decls ~select ~is_header ()) p
  in
  (* A constrained template named ahead of its definition is declared in front
     of the chunk that names it, in the same way; see
     {!Cpp_print.register_forward_struct_decl}. *)
  if is_header && !Cpp_print.constrained_forward_struct_decls <> [] then
    prefix (Cpp_print.take_constrained_forward_decls (Pp.string_of_ppcmds p)) p
  else p

(** The top-level elements a hoisted concept cannot be read without.

    Hoisting a file-scope concept to the top of the file is answered, for
    almost everything it spells, by the forward declarations already in front
    of it: a [requires] body is unevaluated, so a plain mention wants the name
    declared and not defined.  Two kinds want more.  C++ admits no forward
    declaration for a [using], and a name spelled {e qualified} is a member
    lookup in a type that has to be complete.  Both are answered by moving the
    element itself, and the question this asks is which elements those are.

    It is asked of the whole file rather than at each element, because the
    element that has to move is almost always written {e after} the class that
    names it -- Rocq's own order guarantees only that it precedes the class,
    and the concept has left that position.  The answer is by label, which is
    what an element can check about itself while it renders.

    An inductive is spelled qualified when it is written inside a wrapper
    struct rather than merged with it -- [List::list], beside the functions of
    the file module [List] -- and that is a question only the printer's table
    answers ({!Cpp_print.nested_in_wrapper}), so this is asked once the
    wrapper modules have queued their declarations.

    Transitive, and only through the elements themselves: an alias in the set
    spells types that then have to precede {e it}, and one of those may be
    another alias.  A struct in the set wants more than names: its payloads
    and the functions [wrapper_sels] merges into it are written out, so every
    inductive they mention has to be complete there, forward-declared or not.
    It does not descend into a module that is already in the set, because
    moving a struct moves everything in it. *)
let concept_prereqs ~wrapper_sels (s : ml_structure) : Names.Label.Set.t =
  let add_type_refs acc ty =
    let rec go acc = function
      | Miniml.Tglob (r, args, _) ->
        List.fold_left go (Ref.User.Set.add r acc) args
      | Miniml.Tarr (a, b) -> go (go acc a) b
      | Miniml.Tmeta {contents = Some t} -> go acc t
      | _ -> acc
    in
    go acc ty
  in
  let elements =
    List.concat_map
      (fun (mp, ms) -> List.map (fun (l, se) -> (mp, l, se)) ms)
      s
  in
  (* What the file-scope concepts spell: the field types of every type class
     declared here. *)
  let seed =
    List.fold_left
      (fun acc (_, _, se) ->
        match se with
        | Miniml.SEdecl (Miniml.Dind (_, ind)) -> (
          match ind.Miniml.ind_kind with
          | Miniml.TypeClass _ ->
            Array.fold_left
              (fun acc p ->
                Array.fold_left
                  (fun acc tys -> List.fold_left add_type_refs acc tys)
                  acc p.Miniml.ip_types )
              acc ind.Miniml.ind_packets
          | _ -> acc )
        | _ -> acc )
      Ref.User.Set.empty elements
  in
  let packet_refs kn ind =
    List.init (Array.length ind.Miniml.ind_packets) (fun i ->
        GlobRef.IndRef (kn, i) )
  in
  (* What a struct's body writes out: its payloads, and the signatures of the
     functions merged into it. *)
  let body_refs kn ind =
    let payloads =
      Array.fold_left
        (fun acc p ->
          Array.fold_left
            (fun acc tys -> List.fold_left add_type_refs acc tys)
            acc p.Miniml.ip_types )
        Ref.User.Set.empty ind.Miniml.ind_packets
    in
    List.fold_left
      (fun acc r ->
        List.fold_left
          (fun acc (_, se) ->
            match se with
            | Miniml.SEdecl d ->
              List.fold_left
                (fun acc fd -> add_type_refs acc fd.Miniml.fd_type)
                acc (Mlutil.term_defs d)
            | _ -> acc )
          acc
          (wrapper_sels (Cpp_print.nspace_wrapper_name r)) )
      payloads (packet_refs kn ind)
  in
  let label_of (mp, l, se) (needed, complete) =
    match se with
    | Miniml.SEdecl (Miniml.Dtype (r, _, _)) ->
      if Ref.User.Set.mem r needed then Some l else None
    | Miniml.SEdecl (Miniml.Dind (kn, ind)) -> (
      match ind.Miniml.ind_kind with
      | Miniml.TypeClass _ -> None
      | _ ->
        if
          List.exists
            (fun r ->
              Ref.User.Set.mem r complete
              || (Ref.User.Set.mem r needed && Cpp_print.nested_in_wrapper r) )
            (packet_refs kn ind)
        then Some l
        else None )
    | Miniml.SEmodule _ ->
      let inner = MPdot (mp, l) in
      let rec under m =
        ModPath.equal m inner
        || match m with MPdot (m', _) -> under m' | _ -> false
      in
      if
        Ref.User.Set.exists
          (fun r -> under (modpath_of_r r))
          needed
      then Some l
      else None
    | _ -> None
  in
  let rec fixpoint ((needed, complete) as refs) labels =
    let labels', (needed', complete') =
      List.fold_left
        (fun (labels, ((needed, complete) as refs)) ((_, l, se) as e) ->
          match label_of e refs with
          | None -> (labels, refs)
          | Some l' ->
            let labels = Names.Label.Set.add l' labels in
            let refs =
              match se with
              | Miniml.SEdecl (Miniml.Dtype (_, _, ty)) ->
                (add_type_refs needed ty, complete)
              | Miniml.SEdecl (Miniml.Dind (kn, ind)) ->
                let body = body_refs kn ind in
                (Ref.User.Set.union body needed, Ref.User.Set.union body complete)
              | _ -> refs
            in
            (labels, refs) )
        (labels, refs) elements
    in
    if
      Ref.User.Set.equal needed needed'
      && Ref.User.Set.equal complete complete'
      && Names.Label.Set.equal labels labels'
    then labels'
    else fixpoint (needed', complete') labels'
  in
  fixpoint (seed, Ref.User.Set.empty) Names.Label.Set.empty

(** Main structure renderer with declaration tracking.

    PASS 1: Process all wrapper modules to populate pending_wrapper_decls. PASS
    2: Render types and inject pending specs into Dnspace structs. PASS 3: Emit
    deferred function definitions.

    This three-pass approach resolves forward reference issues while maintaining
    proper C++ declaration order.

    @param is_header  When [true] render the header pass (struct definitions,
                      concept declarations, inline specs); when [false] render
                      the implementation pass (out-of-line function bodies).
    @param f          Structure-element callback, typically
                      [pp_structure_elem ~is_header impl_decls] or the [header_decls]
                      variant; called for each [(label, ml_structure_elem)] pair.
    @param s          The flat extraction structure: a list of
                      [(module_path, structure_elem list)] pairs produced by the
                      extraction pipeline.
    @return Pretty-printer document for the complete output file (header or
            implementation), including lifted declarations and deferred
            out-of-line function definitions. *)
let do_struct_with_decl_tracking ~is_header f s =
  (* A synthesised alias is emitted in front of the top-level element whose
     rendering minted it, rather than collected into the file's prologue.

     The prologue is only sound for a body naming top-level class templates:
     those can be forward-declared, so the prologue's forward declarations make
     the names readable there.  A body may name something that cannot be
     forward-declared at all -- a member template of another struct, or another
     alias template -- and then no prologue entry could have helped and the
     alias has to follow the {e definition}.

     The element to go in front of is the one that {e uses} the alias, which is
     not the one that minted it: a use written into a deferred member
     definition is minted while some earlier element is rendering but placed at
     the end of the file, and following the mint puts the declaration hundreds
     of lines ahead of everything the body names.  A use, by contrast, sits in
     code that manipulates values of the types the body names, and so comes
     after their definitions -- as a tendency and not as a guarantee: the use
     spells the alias, not the types inside it, so nothing here forces the
     margin to be positive.  On Vellvm it is about eleven thousand lines, and
     on this corpus the two placements coincide exactly, nothing in it being
     deferred.

     So the alias waits in the registry until some rendered chunk spells it,
     and is emitted in front of that chunk -- which needs no knowledge of what
     the body names, only of where its name appears.  See
     {!prefix_mentioned_aliases}, applied here per top-level element and again
     to each section of the assembled file.

     Only at the outermost call.  [f] recurses through module children, and a
     nested element is rendered inside a struct, where an alias template would
     acquire that struct's scope while its use sites spell it unqualified. *)
  let f =
    let depth = ref 0 in
    fun ((l, _) as x) ->
      incr depth;
      let p = Fun.protect ~finally:(fun () -> decr depth) (fun () -> f x) in
      if !depth <> 0 then
        p
      else
        let p = prefix_mentioned_aliases ~is_header p in
        (* An element the concepts cannot be read without travels with them.
           Decided here rather than inside the element because the question is
           about the file -- see {!concept_prereqs} -- and answered by label
           because that is what the element knows about itself. *)
        if Names.Label.Set.mem l !concept_prereq_labels && not (Pp.ismt p)
        then (
          push file_scope_concept_prereqs p;
          mt () )
        else
          p
  in
  concept_prereq_labels := Names.Label.Set.empty;
  ignore (drain file_scope_concept_prereqs);
  Cpp_print.reset_ctor_alias_emitted ();
  hoisted_module_structs := [];
  Cpp_ind.discard Cpp_ind.deferred_member_defs;
  Cpp_ind.discard Cpp_ind.file_scope_erased_aliases;
  Hashtbl.clear emitted_member_lifted;
  Translation.clear_seen_lifted_refs ();
  init_std_names ();
  (* In Separate Extraction mode the visibility stack is empty when we enter
     here, but analysis helpers (mp_renaming, top_visible, etc.) expect at
     least one entry.  Push the top-level module paths now; they will be
     popped at the end of this function.  The inner per-module push/pop in
     [ppl] adds a second layer which is harmless. *)
  let initial_mps =
    List.filter_map
      (fun (mp, _) -> if is_modfile mp then Some mp else None) s
  in
  List.iter (fun mp -> push_visible mp []) initial_mps;
  let analysis = get_structure_analysis () in
  let is_func_decl (_, se) =
    match se with
    | SEdecl (Dterm _ | Dfix _) -> true
    | _ -> false
  in
  let wrapper_names =
    List.map
      (fun (mi : Structure_analysis.module_info) ->
        ((mi.modpath, mi.sels), mi.wrapper_name) )
      analysis.sorted_modules
  in
  (* Each wrapper module contributes up to three fragments: declarations that
     merge into the struct, and definitions and lifted helpers that must follow
     it.  The struct's declarations go into {!pending_wrapper_decls}, which
     {!Cpp_print} reads when it finds an eponymous type to merge them into; the
     other two stay here, where both producer and consumer are. *)
  let wrapper_parts =
    List.filter_map
      (fun ((mp, sel), wrapper_name) ->
        match wrapper_name with
        | None -> None
        | Some name ->
          push_visible mp [];
          let func_sels = List.filter is_func_decl sel in
          let old_decls = !current_structure_decls in
          current_structure_decls := sel;
          let p_specs, p_defs, p_lifted, p_lifted_specs =
            pp_wrapper_module_dual ~is_header ~wrapper_mp:mp name func_sels
          in
          current_structure_decls := old_decls;
          if not (Pp.ismt p_specs) then (
            Hashtbl.replace pending_wrapper_decls name p_specs;
            Hashtbl.replace unmerged_wrappers name () );
          pop_visible ();
          Some
            {
              wr_name = name;
              wr_defs = p_defs;
              wr_lifted = (if Pp.ismt p_lifted then None else Some p_lifted);
              wr_lifted_specs = p_lifted_specs;
            } )
      wrapper_names
  in
  (* Asked only now, because whether an inductive is written inside a wrapper
     depends on the declarations just queued against it. *)
  if is_header then
    concept_prereq_labels :=
      concept_prereqs s ~wrapper_sels:(fun name ->
          List.concat_map
            (fun ((_, sel), wrapper_name) ->
              if wrapper_name = Some name then List.filter is_func_decl sel
              else [] )
            wrapper_names );
  let joined pick =
    prlist
      (fun part ->
        match pick part with
        | None -> mt ()
        | Some pp -> if Pp.ismt pp then mt () else cut2 () ++ pp )
      wrapper_parts
  in
  let deferred_defs = joined (fun w -> Some w.wr_defs) in
  (* A lifted declaration [ppl] did not get to emit -- its module is not in the
     rendered order -- still has to appear somewhere, so it goes at the end. *)
  let deferred_lifted () = joined (fun w -> w.wr_lifted) in
  (* [ppl] emits a module's lifted declaration when the module's turn comes,
     and empties the field so the tail does not repeat it. *)
  let claim_lifted name =
    match List.find_opt (fun w -> String.equal w.wr_name name) wrapper_parts with
    | Some ({wr_lifted = Some l; _} as w) ->
      w.wr_lifted <- None;
      l
    | _ -> mt ()
  in
  name_cache :=
    Some
      (Name_resolution.create
         ~structure_analysis:analysis
         ~unmerged:unmerged_wrappers
         s );
  let old_local_inductives = get_local_inductives () in
  if modular () then begin
    let rec collect_inductives sel =
      List.iter
        (fun (_l, se) ->
          match se with
          | SEdecl (Dind (kn, ind)) ->
            Array.iteri
              (fun i _p -> add_local_inductive (GlobRef.IndRef (kn, i)))
              ind.ind_packets
          | SEmodule { ml_mod_expr = MEstruct (_, sub_sel); _ } ->
            collect_inductives sub_sel
          | _ -> () )
        sel
    in
    List.iter
      (fun ((_mp, sel), _wrapper_name) -> collect_inductives sel)
      wrapper_names
  end;
  let ppl ((mp, sel), wrapper_name) =
    let old_decls = !current_structure_decls in
    current_structure_decls := sel;
    push_visible mp [];
    let p =
      match wrapper_name with
      | Some name ->
        let type_sels = List.filter (fun x -> not (is_func_decl x)) sel in
        let type_pp = prlist_sep_nonempty cut2 f type_sels in
        (* The wrapper struct belongs at its module's own place in the
           topological order, whether or not the module also declares types.
           A later module's constant is initialised inside its struct body, so
           a callee's struct has to be complete by then -- emitting the
           wrapper after everything else, as a leftover, is too late.  A
           module whose types include an eponymous struct has already had the
           specs merged into it by {!Cpp_print}, and nothing is pending. *)
        let wrapper_pp =
          if not is_header then mt ()
          else
            match Hashtbl.find_opt pending_wrapper_decls name with
            | Some specs ->
              Hashtbl.remove pending_wrapper_decls name;
              let struct_pp = pp_wrapper_struct name specs in
              if
                module_members_name_only_inductives sel
                && module_struct_is_hoistable (Pp.string_of_ppcmds struct_pp)
              then (
                hoisted_module_structs := struct_pp :: !hoisted_module_structs;
                mt () )
              else struct_pp
            | None -> mt ()
        in
        (* A declaration lifted out of this module -- an instance struct -- is
           due at the same point, and for the same reason: a later module's
           constant may be initialised from it. *)
        let lifted_pp = claim_lifted name in
        (* The wrapper struct and what was lifted out of it are elements of
           their own, assembled here rather than by [f]: an alias they spell
           goes in front of them, not in front of the whole section they end
           up in (see {!prefix_mentioned_aliases}). *)
        let wrapper_pp = prefix_mentioned_aliases ~is_header wrapper_pp in
        let lifted_pp = prefix_mentioned_aliases ~is_header lifted_pp in
        prlist_sep_nonempty cut2 (fun x -> x) [type_pp; wrapper_pp; lifted_pp]
      | None ->
        (* Which children a name collision forces inside a wrapper struct is
           layout, decided by {!Structure_analysis} before any rendering began;
           here we only read the answer back. *)
        let is_colliding_child l _se =
          Module_plan.wrapper_role (MPdot (mp, l)) = Some Module_plan.Flattened
        in
        (* Whether a wrapper formed is not the same question as which children
           it flattens: a bystander is recorded only when one did, so a child
           in either table says the struct is there to be written. *)
        let is_wrapped_child l =
          match Module_plan.wrapper_role (MPdot (mp, l)) with
          | Some (Flattened | Bystander) -> true
          | Some Own | None -> false
        in
        let has_child_collision =
          List.exists
            (fun (l, se) ->
              match se with SEmodule _ -> is_wrapped_child l | _ -> false )
            sel
        in
        if has_child_collision then (
          (* The wrapper's name was chosen with the collision that forced it in
             view, by {!Structure_analysis}; each wrapped child records it. *)
          let parent_name =
            List.find_map
              (fun (l, se) ->
                match se with
                | SEmodule _ when is_wrapped_child l ->
                  Module_plan.wrapper_struct (MPdot (mp, l))
                | _ -> None )
              sel
            |> Option.default
                 (Table.escape_reserved_struct_name
                    (String.capitalize_ascii (string_of_modfile mp)))
          in
          if is_header then
            (* A module type is a concept, and C++ has no member concepts, so
               one written among a wrapper's children cannot stay there -- and
               cannot simply move ahead of the wrapper either, because a
               functor elsewhere may be constrained by it and be emitted
               first.  It goes where the concepts of a nested module's
               typeclasses already go, which is the top of the file.  Being
               unwritable inside the struct used to be answered by dropping
               it. *)
            let modtype_sels, sel =
              List.partition
                (fun (_, se) -> match se with SEmodtype _ -> true | _ -> false)
                sel
            in
            List.iter
              (fun x ->
                let pp = f x in
                if not (Pp.ismt pp) then
                  push file_scope_concepts pp )
              modtype_sels;
            let non_colliding_pp, colliding_pp =
              with_render_ctx
                (fun c -> { c with rc_in_struct = true })
                (fun () ->
                  let non_colliding =
                    List.filter
                      (fun (l, se) ->
                        match se with
                        | SEmodule se_inner ->
                          not (is_colliding_child l (SEmodule se_inner))
                        | _ -> true )
                      sel
                  in
                  let non_colliding_pp =
                    prlist_sep_nonempty cut2 f non_colliding
                  in
                  let colliding_pp =
                    prlist_sep_nonempty
                      cut2
                      (fun (_l, se) ->
                        match se with
                        | SEmodule m ->
                          ( match m.ml_mod_expr with
                          | MEstruct (inner_mp, inner_sel) ->
                            push_visible inner_mp [];
                            let inner_func_sels =
                              List.filter is_func_decl inner_sel
                            in
                            let body =
                              prlist_sep_nonempty cut2 f inner_func_sels
                            in
                            pop_visible ();
                            body
                          | _ -> mt () )
                        | _ -> mt () )
                      (List.filter
                         (fun (l, se) -> is_colliding_child l se)
                         sel )
                  in
                  (non_colliding_pp, colliding_pp) )
            in
            let body =
              if Pp.ismt non_colliding_pp then
                colliding_pp
              else if Pp.ismt colliding_pp then
                non_colliding_pp
              else
                non_colliding_pp ++ cut2 () ++ colliding_pp
            in
            let struct_pp =
              if Pp.ismt body then
                mt ()
              else
                str "struct "
                ++ str parent_name
                ++ str " {"
                ++ fnl ()
                ++ body
                ++ fnl ()
                ++ str "};"
            in
            struct_pp
          else
            let non_colliding_pp, colliding_pp =
              with_render_ctx
                (fun c ->
                  { c with
                    rc_struct_name = Some (str parent_name);
                    rc_struct_mp = Some mp } )
                (fun () ->
                  let non_colliding =
                    List.filter
                      (fun (l, se) ->
                        match se with
                        | SEmodule se_inner ->
                          not (is_colliding_child l (SEmodule se_inner))
                        | _ -> true )
                      sel
                  in
                  let non_colliding_pp =
                    prlist_sep_nonempty cut2 f non_colliding
                  in
                  let colliding_pp =
                    prlist_sep_nonempty
                      cut2
                      (fun (_l, se) ->
                        match se with
                        | SEmodule m ->
                          ( match m.ml_mod_expr with
                          | MEstruct (inner_mp, inner_sel) ->
                            push_visible inner_mp [];
                            let body = prlist_sep_nonempty cut2 f inner_sel in
                            pop_visible ();
                            body
                          | _ -> mt () )
                        | _ -> mt () )
                      (List.filter
                         (fun (l, se) -> is_colliding_child l se)
                         sel )
                  in
                  (non_colliding_pp, colliding_pp) )
            in
            let body =
              if Pp.ismt non_colliding_pp then
                colliding_pp
              else if Pp.ismt colliding_pp then
                non_colliding_pp
              else
                non_colliding_pp ++ cut2 () ++ colliding_pp
            in
            body )
        else
          prlist_sep_nonempty cut2 f sel
    in
    current_structure_decls := old_decls;
    if modular () then pop_visible ();
    p
  in
  let rendered = List.map (fun wn -> (wn, ppl wn)) wrapper_names in
  if modular () then begin
    clear_local_inductives ();
    List.iter add_local_inductive old_local_inductives
  end;
  (* Every pending name came from [wrapper_names], and rendering that module in
     the header consumes it: either {!Cpp_print} merged the specs into an
     eponymous struct, or [ppl] emitted them as a struct of their own.  A name
     still pending there is one whose module was never rendered, and emitting
     it as a leftover at the end of the file would put it after its users.  The
     implementation file declares no wrapper structs at all, so specs left
     pending by its pass are simply unused. *)
  if is_header && Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    Hashtbl.iter
      (fun name _ ->
        CErrors.user_err
          Pp.(
            str "Crane: wrapper struct '" ++ str name
            ++ str "' was never emitted: its module is not in the rendered \
                    order." ) )
      pending_wrapper_decls;
  Hashtbl.clear pending_wrapper_decls;
  let rev_rendered = List.rev rendered in
  let main_entry, pre_entries =
    match rev_rendered with
    | ((_, None), p) :: rest -> (Some p, List.rev rest)
    | _ -> (None, rendered)
  in
  let p_pre = prlist_sep_nonempty cut2 snd pre_entries in
  let p =
    prlist_sep_nonempty cut2 (fun x -> x)
      ( match main_entry with
      | Some main_p -> [p_pre; main_p]
      | None -> [p_pre] )
  in
  if not (modular ()) then
    repeat (List.length wrapper_names) pop_visible ();
  (* Pop the initial visibility entries pushed at the top of this function. *)
  List.iter (fun _ -> pop_visible ()) initial_mps;
  let hoisted_erased_aliases =
    let imports = List.map str (Cpp_print.take_promoted_alias_imports ()) in
    match imports @ Cpp_ind.render_deferred Cpp_ind.file_scope_erased_aliases with
    | [] -> mt ()
    | l -> prlist_with_sep fnl (fun x -> x) l ++ cut2 ()
  in
  let hoisted_concept_prereqs =
    match drain file_scope_concept_prereqs with
    | [] -> mt ()
    | l -> prlist_with_sep cut2 (fun x -> x) l ++ cut2 ()
  in
  let hoisted_concepts =
    match drain file_scope_concepts with
    | [] -> mt ()
    | l -> prlist_with_sep cut2 (fun x -> x) l ++ cut2 ()
  in
  let forward_decls =
    let structs =
      if is_header then Cpp_print.take_forward_struct_decls ()
      else (ignore (Cpp_print.take_forward_struct_decls ()); [])
    in
    (* Aliases go in front of the text that uses them; see
       {!prefix_mentioned_aliases}.  Only what no text asked for is left for
       the prologue, and it is collected below, after every section has had
       its turn. *)
    match structs with
    | [] -> mt ()
    | l -> prlist_with_sep fnl (fun x -> x) l ++ cut2 ()
  in
  (* Declared ahead of everything that could call them, which is everything:
     a lifted helper's definition is placed after the struct it came out of,
     and its callers are that struct's members.  This goes after the concepts
     because a helper's constraint may name one, and after the struct forward
     declarations because its parameters may name a struct -- a declaration
     needs those declared, not complete.  Redeclaring a helper that did land
     before its uses is legal and costs a line; deciding which those are would
     cost the property that makes this correct. *)
  let lifted_fun_specs =
    if is_header then
      let parts =
        List.filter_map
          (fun w -> if Pp.ismt w.wr_lifted_specs then None else Some w.wr_lifted_specs)
          wrapper_parts
        @ Cpp_ind.render_deferred pending_lifted_specs
      in
      match List.filter (fun x -> not (Pp.ismt x)) parts with
      | [] -> mt ()
      | l -> prlist_with_sep cut2 (fun x -> x) l ++ cut2 ()
    else
      mt ()
  in
  (* Alongside the lifted helpers and for the same reason, in front of them
     because a helper's own declaration may name one of these. *)
  let hoisted_wrappers =
    match List.rev !hoisted_module_structs with
    | [] -> mt ()
    | l ->
      hoisted_module_structs := [];
      prlist_with_sep cut2 (fun x -> x) l ++ cut2 ()
  in
  (* Last of all: a datatype's method whose body names a module's struct, which
     is emitted after every datatype.  Nothing else in the header is later. *)
  let deferred_members =
    match Cpp_ind.render_deferred Cpp_ind.deferred_member_defs with
    | [] -> mt ()
    | ds -> cut2 () ++ prlist_with_sep cut2 (fun x -> x) ds
  in
  let deferred_lifted = deferred_lifted () in
  (* In writing order, so that an alias no single element claimed -- one whose
     only use is in a section assembled out of several -- still lands in front
     of the first section that spells it rather than in the prologue. *)
  let sections =
    List.map (prefix_mentioned_aliases ~is_header)
      [ hoisted_erased_aliases; hoisted_concept_prereqs; hoisted_concepts; hoisted_wrappers; lifted_fun_specs; p;
        deferred_lifted; deferred_defs; deferred_members ]
  in
  (* Whatever nothing spelled.  A body may still name something defined later,
     which is the case the placement above exists for, but an alias with no use
     in the file has no later position to be after either. *)
  Cpp_print.reset_constrained_forward_decls ();
  let leftover_aliases =
    match Cpp_print.take_ctor_alias_decls ~is_header () with
    | [] -> mt ()
    | l -> prlist_with_sep fnl (fun x -> x) l ++ cut2 ()
  in
  (forward_decls ++ leftover_aliases ++ prlist (fun x -> x) sections)
  ++ fnl ()

(** Main entry point: render structure to C++ implementation file. *)
let pp_struct s =
  do_struct_with_decl_tracking
    ~is_header:false
    (pp_structure_elem ~is_header:false impl_decls)
    s

(** Main entry point: render structure to C++ header file. *)
let pp_hstruct s =
  do_struct_with_decl_tracking
    ~is_header:true
    (pp_structure_elem ~is_header:true header_decls)
    s

(** Language descriptor for C++ extraction. *)
let cpp_descr =
  {
    keywords;
    global_scope_keywords = c_library_globals;
    file_suffix = ".cpp";
    file_naming = file_of_modfile;
    preamble;
    pp_struct;
    pp_hstruct;
    sig_suffix = Some ".h";
    sig_preamble;
    pp_decl = (fun d -> pp_decls (impl_decls d).rendered);
  }
