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
open Modutil
open Common
open Minicpp
open Translation
open Cpp_state
open Cpp_names
open Cpp_print
open Cpp_ind

(** Parse a custom type template string (e.g., "std::optional<%t0>",
    "std::vector<%t0>", "std::pair<%t0,%t1>") and recursively qualify type
    arguments using the provided qualify_type function.

    This allows any parametric custom type to have its inner type arguments
    properly qualified with "typename M::" when used in module signature
    requires clauses.

    @param custom_str  The raw custom-type annotation string; [%t0], [%t1], …
                       are placeholder tokens replaced by the corresponding
                       elements of [args].
    @param args        The ML type arguments to substitute for the [%tN]
                       placeholders, in order.
    @param qualify_type  Recursive callback that qualifies a single ML type
                         (e.g. prepending ["typename M::"]) before splicing it
                         into the output.
    @return Pretty-printer document with all [%tN] placeholders replaced by
            their qualified type renderings and surrounding literal text
            preserved verbatim. *)
let qualify_custom_template custom_str args qualify_type =
  let len = String.length custom_str in
  let rec parse i result =
    if i >= len then
      result
    else if i <= len - 3 && custom_str.[i] = '%' && custom_str.[i + 1] = 't'
    then
      let digit_start = i + 2 in
      let rec find_digit_end j =
        if j < len && custom_str.[j] >= '0' && custom_str.[j] <= '9' then
          find_digit_end (j + 1)
        else
          j
      in
      let digit_end = find_digit_end digit_start in
      if digit_end > digit_start then
        let num_str =
          String.sub custom_str digit_start (digit_end - digit_start)
        in
        let idx = int_of_string num_str in
        if idx < List.length args then
          parse digit_end (result ++ qualify_type (List.nth args idx))
        else
          parse
            digit_end
            (result ++ str (String.sub custom_str i (digit_end - i)))
      else
        parse (i + 1) (result ++ str (String.make 1 custom_str.[i]))
    else
      let rec find_next j =
        if j >= len then
          len
        else if custom_str.[j] = '%' then
          j
        else
          find_next (j + 1)
      in
      let next = find_next (i + 1) in
      parse next (result ++ str (String.sub custom_str i (next - i)))
  in
  parse 0 (mt ())

(** Pretty-print a structure signature element (module spec). *)
let rec pp_specif = function
  | _, Spec (Sval _ as s) -> pp_spec s
  | l, Spec s ->
    ( match Common.get_duplicate (top_visible_mp ()) l with
    | None -> pp_spec s
    | Some ren -> pp_spec s )
  | l, Smodule mt ->
    let def = pp_module_type [] mt in
    def
    ++
    ( match Common.get_duplicate (top_visible_mp ()) l with
    | None -> Pp.mt ()
    | Some ren -> fnl () )
  | l, Smodtype mt ->
    let def = pp_module_type [] mt in
    let name = pp_modname (MPdot (top_visible_mp (), l)) in
    hov 1 (str "module type " ++ name ++ str " =" ++ fnl () ++ def)
    ++
    ( match Common.get_duplicate (top_visible_mp ()) l with
    | None -> Pp.mt ()
    | Some ren -> fnl () ++ str ("module type " ^ ren ^ " = ") ++ name )

(** Check if a ML type contains type variables (for module signature
    requirements).

    This enables compile-time checking that modules satisfy their type
    signatures. *)
and ml_type_has_tvar = function
  | Miniml.Tvar _ | Miniml.Tvar' _ -> true
  | Miniml.Tunknown -> true
  | Miniml.Tarr (t1, t2) -> ml_type_has_tvar t1 || ml_type_has_tvar t2
  | Miniml.Tglob (_, args, _) -> List.exists ml_type_has_tvar args
  | Miniml.Tmeta {contents = Some t} -> ml_type_has_tvar t
  | Miniml.Tmeta {contents = None} -> true
  | _ -> false

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
and pp_spec_as_requirement modtype_mp modtype_refs = function
  | Sval (r, _, _) when is_inline_custom r -> mt ()
  | Stype (r, _, _) when is_inline_custom r -> mt ()
  | Sind (kn, i) ->
    let name = pp_global_name Type (GlobRef.IndRef (kn, 0)) in
    str "typename M::" ++ name ++ str ";" ++ fnl ()
  | Sval (r, _, t) when ml_type_has_tvar t -> mt ()
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
      convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ret_ty
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
    let is_member_ref r =
      let rmp = modpath_of_r r in
      let rec get_base_mp = function
        | MPdot (parent, _) -> get_base_mp parent
        | mp -> mp
      in
      is_mp_under modtype_mp rmp
      || (match get_base_mp rmp with MPbound _ -> true | _ -> false)
    in
    let rec qualify_type = function
      | Tglob (r, [], _) when not (is_custom r) && is_member_ref r ->
        str "typename M::" ++ pp_global Type r
      | Tglob (r, args, _) when not (is_custom r) && is_member_ref r ->
        str "typename M::template "
        ++ pp_global Type r
        ++ str "<"
        ++ prlist_with_sep (fun () -> str ", ") qualify_type args
        ++ str ">"
      | Tglob (r, args, _) ->
        ( match find_custom_opt r with
        | Some custom_str ->
          if String.contains custom_str '%' then
            qualify_custom_template custom_str args qualify_type
          else
            str custom_str
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
      | Tunique_ptr ty ->
        str stdlib_ns ++ str "unique_ptr<" ++ qualify_type ty ++ str ">"
      | Tvariant tys ->
        str stdlib_ns
        ++ str "variant<"
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
           pp_cpp_type and render as std::function<bool(elt)> — elt is bare.
           We need std::function<bool(typename M::elt)>. *)
        require_header "functional";
        str stdlib_ns ++ str "function<"
        ++ qualify_type c
        ++ str "("
        ++ prlist_with_sep (fun () -> str ", ") qualify_type d
        ++ str ")>"
      | ty -> pp_cpp_type false [] ty
    in
    if args = [] then
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
          (convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [])
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
  | MPdot (mp0, l') ->
    if get_force_qualified_capitalization () then begin
      (* Separate extraction: pp_modname produces visibility-aware names. *)
      let name = pp_modname kn in
      let name_str = Pp.string_of_ppcmds name in
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
         && not (is_qualified_name name_str) then
        name ++ str "::" ++ str (Label.to_string l')
      else
        name
    end else begin
      (* Monolithic extraction: pp_module may over-qualify same-module
         concepts because the visibility context shifts inside
         pp_module_type.  Keep the short label and just trigger include
         tracking. *)
      ignore (Common.pp_module kn);
      str (Label.to_string l')
    end
  | _ -> pp_modname kn

(** Convert a module type to a C++20 concept. MTsig generates requires clauses,
    MTfunsig is handled by param tracking, MTident references an existing
    concept by name.

    @param params  Accumulated list of bound module-path parameters introduced
                   by enclosing [MTfunsig] binders.  These are pushed onto the
                   visibility stack when an [MTsig] body is entered so that
                   functor-parameter references resolve correctly.
    @return Pretty-printer document containing the [requires { … }] body, a
            bare concept name (for [MTident]), or [mt ()] when the module type
            carries no extractable constraints. *)
and pp_module_type params = function
  | MTident kn -> pp_modname kn
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
        let def = pp_module_type [] nested_mt in
        let modtype_name = str (Label.to_string label) in
        let concept_pp =
          if Pp.ismt def then
            str "template<typename M>"
            ++ fnl ()
            ++ hov 1 (str "concept " ++ modtype_name ++ str " = true;")
          else
            str "template<typename M>"
            ++ fnl ()
            ++ hov
                 1
                 ( str "concept "
                 ++ modtype_name
                 ++ str " = requires {"
                 ++ fnl ()
                 ++ def
                 ++ str "};" )
        in
        hoisted_concept_defs := concept_pp :: !hoisted_concept_defs;
        mt ()
    in
    let reqs = List.map pp_req sign in
    let reqs = List.filter (fun p -> not (Pp.ismt p)) reqs in
    pop_visible ();
    if List.is_empty reqs then
      mt ()
    else
      prlist identity reqs
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

(** Pretty-print a structure element (label, elem) pair. Handles modules, module
    types, and declarations.

    @param is_header  When [true], emit header-mode output (struct definitions,
                      concept declarations, [using] aliases).  When [false],
                      emit implementation-mode output (out-of-line function
                      bodies, skipping header-only constructs).
    @param f          Callback used to pretty-print individual {!Miniml.ml_decl}
                      nodes; typically [pp_decl] or [pp_hdecl].
    @return Pretty-printer document for the element, or [mt ()] if the element
            produces no output in the current pass. *)
let rec pp_structure_elem ~is_header f = function
  | l, SEdecl d ->
    let body = f d in
    if Pp.ismt body then
      mt ()
    else
      let doc = pp_doc_comment l in
      ( match Common.get_duplicate (top_visible_mp ()) l with
      | None -> doc ++ body
      | Some ren ->
        doc
        ++ v 1 (str ("namespace " ^ ren ^ " {") ++ fnl () ++ body)
        ++ fnl ()
        ++ str "};" )
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
           we compute the label name without registering it. *)
        let s = Common.module_label_name l in
        str (Table.escape_reserved_struct_name s)
      | _ ->
        let raw = pp_modname mp in
        let s = Pp.string_of_ppcmds raw in
        let escaped = Table.escape_reserved_struct_name s in
        if String.equal s escaped then raw else str escaped
    in
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
          (* Try to extract a named concept from a module type.

             Strips MTwith constraints (which have no C++ concept equivalent)
             and MTfunsig parameter layers, looking for an MTident that
             references an already-defined concept.  Returns None for
             anonymous inline signatures (MTsig).

             This is important for functor parameters like
             [c' : C b' with Module a := A_instance].  Rocq's extraction
             expands MEapply (module type application) into an inline MTsig,
             losing the reference to the named concept C.  Without this
             helper, pp_module_type would inline the concept body into the
             template parameter list, producing garbled C++. *)
          let rec get_concept_name_from_mt = function
            | MTident kn -> Some (pp_concept_ref kn)
            | MTwith (mt, _) -> get_concept_name_from_mt mt
            | MTfunsig (_, _, mt') -> get_concept_name_from_mt mt'
            | MTsig _ -> None
          in
          (* Render a functor parameter as a C++ template parameter.

             Strategy:
             - If a named concept can be extracted from the module type via
               get_concept_name_from_mt, emit [ConceptName param_name].
             - If the module type has no constraints (empty concept body),
               emit [typename param_name] (unconstrained type parameter).
             - If the concept body is complex (multi-line or >40 chars) —
               typically from MEapply expansion of a parameterised module
               type — fall back to [typename param_name] rather than
               inlining the unreadable requires body.
             - Otherwise use the simple concept body as a constraint. *)
          let pp_template_param (mbid, mt) =
            let param_name = pp_modname (MPbound mbid) in
            match get_concept_name_from_mt mt with
            | Some cname -> cname ++ str " " ++ param_name
            | None ->
              let concept_body = pp_module_type [] mt in
              if Pp.ismt concept_body then
                str "typename " ++ param_name
              else
                let body_str = Pp.string_of_ppcmds concept_body in
                if String.contains body_str '\n'
                   || String.length body_str > 40 then
                  str "typename " ++ param_name
                else
                  concept_body ++ str " " ++ param_name
          in
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
              ~setup:(fun () ->
                render_ctx.rc_in_struct <- true;
                render_ctx.rc_in_template <- true )
              (fun () ->
                pp_module_expr
                  ~is_header
                  f
                  (List.map (fun (mbid, _) -> MPbound mbid) template_params)
                  body )
          in
          (match body with
          | MEapply _ ->
            let () =
              let rec get_base_fmp = function
                | MEapply (f, _) -> get_base_fmp f
                | MEident fmp -> Some fmp
                | _ -> None
              in
              match get_base_fmp body with
              | Some fmp -> Hashtbl.replace functor_app_sources mp fmp
              | None -> ()
            in
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
          let rec get_base_functor_mp = function
            | MEapply (f, _) -> get_base_functor_mp f
            | MEident fmp -> Some fmp
            | _ -> None
          in
          ( match get_base_functor_mp m.ml_mod_expr with
          | Some fmp -> Hashtbl.replace functor_app_sources mp fmp
          | None -> () );
          let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
          let using_decl =
            str "using " ++ name ++ str " = " ++ body ++ str ";"
          in
          let rec get_concept_name = function
            | MTident kn -> Some (pp_concept_ref kn)
            | MTwith (mt, _) -> get_concept_name mt
            | MTfunsig (_, mt, mt') -> get_concept_name mt'
            | MTsig _ -> None
          in
          let static_assert =
            match get_concept_name m.ml_mod_type with
            | Some concept_name ->
              fnl ()
              ++ str "static_assert("
              ++ concept_name
              ++ str "<"
              ++ name
              ++ str ">);"
            | None -> mt ()
          in
          using_decl ++ static_assert
      | MEstruct (_mp, sel) ->
        let old_context = render_ctx.rc_in_struct in
        let old_struct_name = render_ctx.rc_struct_name in
        let old_struct_mp = render_ctx.rc_struct_mp in
        let old_eponymous = !eponymous_type_ref in
        let old_methods = !method_candidates in
        let old_eponymous_record = !eponymous_record in
        eponymous_type_ref := None;
        eponymous_record := None;
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
                      eponymous_record := Some (ind_ref, fields, p);
                      register_eponymous_record ind_ref
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
        | Some epon_ref ->
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
                    if Environ.QGlobRef.equal Environ.empty_env fwd_ref epon_ref
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
                (Environ.QGlobRef.equal Environ.empty_env r)
                excluded_refs
              || List.exists refs_excluded args
            | Miniml.Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
            | Miniml.Tmeta {contents = Some t} -> refs_excluded t
            | _ -> false
          in
          let process_decl (_l, se) =
            match se with
            | SEdecl (Dterm (r, body, ty)) ->
              if same_module r && not (refs_excluded ty) then
                Option.iter
                  (fun c -> method_candidates := c :: !method_candidates)
                  (try_register_method epon_ref r body ty)
            | SEdecl (Dfix (rv, defs, typs)) ->
              Array.iteri
                (fun i r ->
                  if same_module r && not (refs_excluded typs.(i)) then
                    Option.iter
                      (fun c -> method_candidates := c :: !method_candidates)
                      (try_register_method epon_ref r defs.(i) typs.(i)))
                rv
            | _ -> ()
          in
          List.iter process_decl sel;
          List.iter process_decl !current_structure_decls
        | None -> () );
        let this_eponymous_record = !eponymous_record in
        let concept_simple_name_of ind_ref =
          let sn = Common.pp_global_name Type ind_ref in
          match String.rindex_opt sn ':' with
          | Some idx
            when idx > 0 && idx < String.length sn - 1 && sn.[idx - 1] = ':' ->
            String.sub sn (idx + 1) (String.length sn - idx - 1)
          | _ -> sn
        in
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
                        (concept_simple_name_of ind_ref)
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
                         let packet = ind.ind_packets.(i) in
                         let concept_pp =
                           pp_cpp_decl
                             (empty_env ())
                             (Translation.gen_typeclass_cpp
                                ind_ref
                                fields
                                packet )
                         in
                         let doc = pp_doc_comment l in
                         [doc ++ concept_pp]
                       | _ -> [] ) )
                | _ -> [] )
              sel
          else
            []
        in
        let typeclasses_pp =
          prlist_with_sep fnl (fun x -> x) typeclass_concepts
        in
        let typeclasses_pp =
          if typeclass_concepts = [] then
            mt ()
          else
            fnl () ++ typeclasses_pp ++ fnl () ++ fnl ()
        in
        let modtype_concepts =
          if is_header then
            List.filter_map
              (fun (l, se) ->
                match se with
                | SEmodtype m ->
                  let modtype_name = str (Label.to_string l) in
                  let rec get_base_concept = function
                    | MTident kn -> Some kn
                    | MTwith (mt, _) -> get_base_concept mt
                    | _ -> None
                  in
                  let concept_pp =
                    match get_base_concept m with
                    | Some base_kn ->
                      let base_name = pp_concept_ref base_kn in
                      str "template<typename M>"
                      ++ fnl ()
                      ++ hov
                           1
                           ( str "concept "
                           ++ modtype_name
                           ++ str " = "
                           ++ base_name
                           ++ str "<M>;" )
                    | None ->
                      let old_hoisted = !hoisted_concept_defs in
                      hoisted_concept_defs := [];
                      let def = pp_module_type [] m in
                      let hoisted = List.rev !hoisted_concept_defs in
                      hoisted_concept_defs := old_hoisted;
                      let main_concept =
                        if Pp.ismt def then
                          str "template<typename M>"
                          ++ fnl ()
                          ++ hov
                               1
                               (str "concept " ++ modtype_name ++ str " = true;")
                        else
                          str "template<typename M>"
                          ++ fnl ()
                          ++ hov
                               1
                               ( str "concept "
                               ++ modtype_name
                               ++ str " = requires {"
                               ++ fnl ()
                               ++ def
                               ++ str "};" )
                      in
                      let all = List.append hoisted [main_concept] in
                      prlist_with_sep (fun () -> fnl () ++ fnl ()) identity all
                  in
                  Some concept_pp
                | _ -> None )
              sel
          else
            []
        in
        let modtypes_pp = prlist_with_sep fnl (fun x -> x) modtype_concepts in
        let modtypes_pp =
          if modtype_concepts = [] then
            mt ()
          else
            modtypes_pp ++ fnl () ++ fnl ()
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
                            Environ.QGlobRef.equal Environ.empty_env r ind_ref )
                          !eponymous_type_ref
                        = Some true
                      then
                        let param_sign =
                          List.firstn ind.ind_nparams p.ip_sign
                        in
                        let num_param_vars =
                          List.length
                            (List.filter
                               (fun x -> x == Miniml.Keep)
                               param_sign )
                        in
                        found := Some (List.firstn num_param_vars p.ip_vars) )
                    ind.ind_packets;
                  !found
                | _ -> None )
              sel
          else
            None
        in
        (* Save previous promotion state for the eponymous inductive, if any.
           The same inductive may have been promoted when rendered standalone
           but should not be promoted when rendered nested. *)
        let was_previously_promoted =
          match !eponymous_type_ref with
          | Some r -> Hashtbl.mem promoted_inductives r
          | None -> false
        in
        (* Set promotion state before body rendering. *)
        if is_promoted then (
          eponymous_promote_ref := !eponymous_type_ref;
          Option.iter
            (fun r -> Hashtbl.replace promoted_inductives r ())
            !eponymous_type_ref;
          eponymous_deferred := Pp.mt ();
          eponymous_promote_sft := false )
        else
          (* When NOT promoted (e.g., nested context), ensure the eponymous
             inductive is NOT marked as promoted. A previous standalone
             rendering of the same module may have added it. *)
          Option.iter
            (fun r -> Hashtbl.remove promoted_inductives r)
            !eponymous_type_ref;
        let old_in_template = render_ctx.rc_in_template in
        let old_concepts_hoisted = render_ctx.rc_concepts_hoisted in
        if is_header && not has_concept_collision then (
          render_ctx.rc_in_struct <- true;
          (* For promoted modules with template params, set rc_in_template so
             non-inductive defs inside get full inline definitions. *)
          if is_promoted then
            match
              promoted_tparams
            with
            | Some (_ :: _) -> render_ctx.rc_in_template <- true
            | _ -> () )
        else if (not is_header) && not has_concept_collision then (
          render_ctx.rc_struct_name <-
            ( match old_struct_name with
            | Some parent -> Some (parent ++ str "::" ++ name)
            | None -> Some name );
          render_ctx.rc_struct_mp <- Some mp );
        if is_header && typeclass_concepts <> [] then
          render_ctx.rc_concepts_hoisted <- true;
        let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
        let this_method_candidates = !method_candidates in
        render_ctx.rc_in_struct <- old_context;
        render_ctx.rc_in_template <- old_in_template;
        render_ctx.rc_concepts_hoisted <- old_concepts_hoisted;
        render_ctx.rc_struct_name <- old_struct_name;
        render_ctx.rc_struct_mp <- old_struct_mp;
        eponymous_type_ref := old_eponymous;
        eponymous_record := old_eponymous_record;
        method_candidates := old_methods;
        (* Restore promotion state for the eponymous inductive if it was
           previously promoted (before this nested rendering removed it). *)
        if (not is_promoted) && was_previously_promoted then
          Option.iter
            (fun r -> Hashtbl.replace promoted_inductives r ())
            !eponymous_type_ref;
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
                str " : public std::enable_shared_from_this<"
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
            typeclasses_pp ++ modtypes_pp ++ struct_def ++ this_deferred
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
                let field_list = List.combine fields packet.ip_types.(0) in
                let pp_field (field_ref, field_ty) =
                  let field_name =
                    match field_ref with
                    | Some r -> str (Common.pp_global_name Term r)
                    | None -> str "_field"
                  in
                  let cpp_ty =
                    pp_cpp_type
                      false
                      ty_vars
                      (convert_ml_type_to_cpp_type
                         (empty_env ())
                         Refset'.empty
                         ty_vars
                         field_ty )
                  in
                  cpp_ty ++ spc () ++ field_name ++ str ";"
                in
                let fields_pp =
                  prlist_with_sep fnl pp_field field_list ++ fnl ()
                in
                let non_projection_candidates =
                  List.filter
                    (fun (r, _, _, _) -> not (Table.is_projection r))
                    (List.rev this_method_candidates)
                in
                let method_fields =
                  Translation.gen_record_methods
                    epon_ref
                    ty_vars
                    non_projection_candidates
                in
                let methods_with_refs =
                  List.combine non_projection_candidates method_fields
                in
                let methods_pp =
                  if method_fields = [] then
                    mt ()
                  else
                    let saved_methods = !method_candidates in
                    method_candidates := this_method_candidates;
                    let result =
                      prlist_with_sep
                        fnl
                        (fun ((_r, _, _, _), (fld, _vis, _tag)) ->
                          pp_cpp_field (empty_env ()) fld )
                        methods_with_refs
                      ++ fnl ()
                    in
                    method_candidates := saved_methods;
                    result
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
              let rec get_concept_name = function
                | MTident kn -> Some (pp_concept_ref kn)
                | MTwith (mt, _) -> get_concept_name mt
                | MTfunsig (_, mt, mt') -> get_concept_name mt'
                | MTsig _ -> None
              in
              let static_assert =
                match get_concept_name m.ml_mod_type with
                | Some concept_name ->
                  fnl ()
                  ++ str "static_assert("
                  ++ concept_name
                  ++ str "<"
                  ++ name
                  ++ str ">);"
                | None -> mt ()
              in
              typeclasses_pp ++ modtypes_pp ++ struct_def ++ static_assert
        else if this_promoted then
          (* Promoted template: all defs are inline in header, skip .cpp *)
          mt ()
        else
          body
      | MEident _ ->
        if not is_header then
          mt ()
        else
          (* Register MEident module aliases in functor_app_sources so that
             is_accessor can resolve alias chains to find registered accessors. *)
          let () = match m.ml_mod_expr with
          | MEident fmp -> Hashtbl.replace functor_app_sources mp fmp
          | _ -> () in
          let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
          let body_str = Pp.string_of_ppcmds body in
          (* Skip [using] aliases whose target is a [Coq__N] duplicate
             wrapper.  These wrappers are an OCaml-specific qualification
             mechanism from {!Common.add_duplicate}: when an OCaml name is
             shadowed inside its own module, the definition is duplicated
             into a [Coq__N] namespace so that external references can
             still reach it.  In C++, scoped structs and namespaces handle
             qualification differently, making these wrappers unnecessary.
             Moreover, the wrapped namespace may never be emitted (e.g.
             notation-only modules with no computational content), causing
             the [using] alias to reference an undefined type. *)
          if String.length body_str >= 5
             && String.sub body_str 0 5 = "Coq__" then
            mt ()
          else
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
              if target_is_namespace && render_ctx.rc_in_struct then
                mt ()
              else
                let body_with_typename =
                  if render_ctx.rc_in_template && is_qualified_name body_str then
                    str "typename " ++ body
                  else body
                in
                str "using " ++ name ++ str " = " ++ body_with_typename ++ str ";"
            else begin
              (* Functor alias: emit [template<...> using Name = Body<params>;].
                 Re-uses the same template-param rendering as the MEfunctor case. *)
              let rec get_concept_name_from_mt = function
                | MTident kn -> Some (pp_concept_ref kn)
                | MTwith (mt, _) -> get_concept_name_from_mt mt
                | MTfunsig (_, _, mt') -> get_concept_name_from_mt mt'
                | MTsig _ -> None
              in
              let pp_template_param (mbid, mt) =
                let param_name = pp_modname (MPbound mbid) in
                match get_concept_name_from_mt mt with
                | Some cname -> cname ++ str " " ++ param_name
                | None ->
                  let concept_body = pp_module_type [] mt in
                  if Pp.ismt concept_body then
                    str "typename " ++ param_name
                  else
                    let body_str' = Pp.string_of_ppcmds concept_body in
                    if String.contains body_str' '\n'
                       || String.length body_str' > 40 then
                      str "typename " ++ param_name
                    else
                      concept_body ++ str " " ++ param_name
              in
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
      doc ++ mod_pp
  | l, SEmodtype m ->
    if (not is_header) || render_ctx.rc_in_struct then
      mt ()
    else
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      let rec get_base_concept = function
        | MTident kn -> Some kn
        | MTwith (mt, _) -> get_base_concept mt
        | _ -> None
      in
      let concept_pp =
        match get_base_concept m with
        | Some base_kn ->
          let base_name = pp_concept_ref base_kn in
          hov 1 (str "concept " ++ name ++ str " = " ++ base_name ++ str "<M>;")
        | None ->
          let old_hoisted = !hoisted_concept_defs in
          hoisted_concept_defs := [];
          let def = pp_module_type [] m in
          let hoisted = List.rev !hoisted_concept_defs in
          hoisted_concept_defs := old_hoisted;
          let hoisted_pp =
            if hoisted = [] then
              mt ()
            else
              prlist_with_sep fnl identity hoisted ++ fnl () ++ fnl ()
          in
          let body =
            if Pp.ismt def then
              hov 1 (str "concept " ++ name ++ str " = true;")
            else
              hov
                1
                ( str "concept "
                ++ name
                ++ str " = requires {"
                ++ fnl ()
                ++ def
                ++ str "};" )
          in
          hoisted_pp ++ body
      in
      str "template<typename M>"
      ++ fnl ()
      ++ concept_pp
      ++
      ( match Common.get_duplicate (top_visible_mp ()) l with
      | None -> mt ()
      | Some ren ->
        fnl ()
        ++ str ("template<typename M> concept " ^ ren ^ " = ")
        ++ name
        ++ str "<M>;" )

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
  | MEapply (me, me') ->
    let rec collect_args acc = function
      | MEapply (f, arg) -> collect_args (arg :: acc) f
      | base -> (base, acc)
    in
    let base, args = collect_args [me'] me in
    let base_pp = pp_module_expr ~is_header f [] base in
    let pp_module_arg arg =
      let arg_pp = pp_module_expr ~is_header f [] arg in
      if render_ctx.rc_in_template then
        let s = Pp.string_of_ppcmds arg_pp in
        if is_qualified_name s then str "typename " ++ arg_pp
        else arg_pp
      else arg_pp
    in
    let args_pp =
      prlist_with_sep (fun () -> str ", ") pp_module_arg args
    in
    let base_pp =
      if render_ctx.rc_in_template then
        let s = Pp.string_of_ppcmds base_pp in
        if is_qualified_name s then
          match
            String.rindex_opt s ':'
          with
          | Some i when i > 0 && s.[i - 1] = ':' ->
            str (String.sub s 0 (i - 1))
            ++ str "::template "
            ++ str (String.sub s (i + 1) (String.length s - i - 1))
          | _ -> base_pp
        else
          base_pp
      else
        base_pp
    in
    base_pp ++ str "<" ++ args_pp ++ str ">"
  | MEfunctor (mbid, mt, me) ->
    pp_module_expr ~is_header f (MPbound mbid :: params) me
  | MEstruct (mp, sel) ->
    push_visible mp params;
    let old_structure_decls = !current_structure_decls in
    current_structure_decls := sel;
    let old_local_inductives = get_local_inductives () in
    List.iter
      (fun (_l, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          Array.iteri
            (fun i _p -> add_local_inductive (GlobRef.IndRef (kn, i)))
            ind.ind_packets
        | _ -> () )
      sel;
    let try_pp_structure_elem l x =
      let px = pp_structure_elem ~is_header f x in
      if Pp.ismt px then l else px :: l
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
      v 1 (prlist_with_sep cut2 identity l) ++ fnl ()

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
    if Pp.ismt e then r else e ++ sep () ++ r

(** Process a wrapper module in dual-pass mode (header vs implementation).

    PASS 1 (is_header=true): Emit forward declarations (specs) for functions.
    PASS 2 (is_header=false): Emit full definitions (defs) for functions.

    The is_header parameter controls which definitions are generated via
    gen_dfuns_dual/gen_decl_for_pp_dual.

    @param is_header   When [true] produce declaration specs; when [false]
                       produce out-of-line definitions.
    @param wrapper_mp  The module path of the wrapper module being rendered;
                       used to set [rc_struct_mp] so that out-of-line
                       definitions are correctly qualified.
    @param wrapper_name  The C++ struct name of the wrapper (e.g. ["Facts"]);
                         used to set [rc_struct_name] in the definition pass.
    @param func_sels   The [(label, structure_elem)] pairs from the wrapper
                       that contain function declarations ([Dterm], [Dfix]).
    @return A triple [(specs_pp, defs_pp, lifted_pp)] where [specs_pp] is the
            header-pass declaration block, [defs_pp] the implementation-pass
            definition block, and [lifted_pp] any top-level declarations that
            were lifted out of local function bodies during translation. *)
let lifted_decl_key = function
  | Dtemplate (_, _, Dfundef ([(GlobRef.VarRef v, _)], _, _, _, _)) ->
    Some (Id.to_string v)
  | Dfundef ([(GlobRef.VarRef v, _)], _, _, _, _) ->
    Some (Id.to_string v)
  | _ -> None

let dedup_lifted_decls ds =
  let seen = Hashtbl.create 16 in
  List.filter (fun d ->
    match lifted_decl_key d with
    | Some k ->
      if Hashtbl.mem seen k then false
      else (Hashtbl.replace seen k (); true)
    | None -> true
  ) ds

let pp_wrapper_module_dual ~is_header ~wrapper_mp wrapper_name func_sels =
  let is_method_candidate x =
    List.exists
      (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env x r')
      !method_candidates
  in
  let process_sel (_l, se) =
    match se with
    | SEdecl (Dterm (r, _, _)) when is_any_inline_custom r -> ([], [], [])
    | SEdecl (Dterm (r, _, _)) when is_eponymous_record_projection r ->
      ([], [], [])
    | SEdecl (Dterm (r, _, _)) when is_suppressed_projection r -> ([], [], [])
    | SEdecl (Dterm (r, _, _)) when is_method_candidate r -> ([], [], [])
    | SEdecl (Dterm (r, body, ty)) when is_registered_method r <> None ->
      ( match is_registered_method r with
      | Some (epon_ref, pos) ->
        let reg = get_method_registry () in
        let already =
          List.exists
            (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r')
            (Method_registry.get_candidates reg epon_ref)
        in
        if not already then
          Method_registry.add_candidate reg epon_ref (r, body, ty, pos)
      | None -> () );
      ([], [], [])
    | SEdecl (Dterm (r, _a, Tglob (ty, _args, _e))) when is_monad ty ->
      ([], [], [])
    | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t -> ([], [], [])
    | SEdecl (Dterm (r, a, t)) ->
      let spec_opt, def_opt, _tvars = gen_decl_for_pp_dual ~is_header r a t in
      let lifted = Translation.take_lifted_decls () in
      let specs =
        match spec_opt with
        | Some s -> [s]
        | None -> []
      in
      let defs =
        match def_opt with
        | Some d -> [d]
        | None -> []
      in
      (specs, defs, lifted)
    | SEdecl (Dfix (rv, defs, typs)) ->
      Array.iteri
        (fun i r ->
          match is_registered_method r with
          | Some (epon_ref, pos) ->
            let reg = get_method_registry () in
            let already =
              List.exists
                (fun (r', _, _, _) ->
                  Environ.QGlobRef.equal Environ.empty_env r r' )
                (Method_registry.get_candidates reg epon_ref)
            in
            if not already then
              Method_registry.add_candidate
                reg
                epon_ref
                (r, defs.(i), typs.(i), pos)
          | None -> () )
        rv;
      let rv, defs, typs = filter_dfix rv defs typs in
      if Array.length rv = 0 then
        ([], [], [])
      else
        let results = gen_dfuns_dual ~is_header (rv, defs, typs) in
        let specs = List.map (fun (s, _, _) -> s) results in
        let defs_list = List.filter_map (fun (_, d, _) -> d) results in
        let lifted = List.concat_map (fun (_, _, l) -> l) results in
        (specs, defs_list, lifted)
    | _ -> ([], [], [])
  in
  let all_results = List.map process_sel func_sels in
  (* Pre-register all Dfix function definitions for mutual recursion detection.
     When functions from a mutual fixpoint (Dfix) are rendered individually,
     each gets loopified independently via maybe_loopify.  Without
     pre-registration, the second function can't see the first in the mutual
     table because the first was already rendered. *)
  List.iter
    (fun (_, defs, _) ->
      List.iter
        (fun (ds, _env) ->
          match ds with
          | Dfundef (names, _, params, body, _) ->
            Loopify.register_fundef names params body
          | Dtemplate (_, _, Dfundef (names, _, params, body, _)) ->
            Loopify.register_fundef names params body
          | _ -> () )
        defs )
    all_results;
  let all_lifted =
    List.concat_map (fun (_, _, l) -> l) all_results
    |> dedup_lifted_decls in
  let render_sel_specs (specs, _, _) =
    match specs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) specs
  in
  let render_sel_defs (_, defs, _) =
    match defs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) defs
  in
  let specs_pp =
    with_render_ctx
      ~setup:(fun () -> render_ctx.rc_in_struct <- true)
      (fun () -> prlist_sep_nonempty cut2 render_sel_specs all_results)
  in
  let defs_pp =
    with_render_ctx
      ~setup:(fun () ->
        render_ctx.rc_struct_name <- Some (str wrapper_name);
        render_ctx.rc_struct_mp <- Some wrapper_mp )
      (fun () -> prlist_sep_nonempty cut2 render_sel_defs all_results)
  in
  let lifted_pp =
    if is_header then
      prlist_sep_nonempty
        cut2
        (fun d -> pp_cpp_decl (empty_env ()) d)
        all_lifted
    else
      mt ()
  in
  (specs_pp, defs_pp, lifted_pp)

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
                      [pp_structure_elem ~is_header pp_decl] or the [pp_hdecl]
                      variant; called for each [(label, ml_structure_elem)] pair.
    @param s          The flat extraction structure: a list of
                      [(module_path, structure_elem list)] pairs produced by the
                      extraction pipeline.
    @return Pretty-printer document for the complete output file (header or
            implementation), including lifted declarations and deferred
            out-of-line function definitions. *)
let do_struct_with_decl_tracking ~is_header f s =
  ignore (Translation.take_lifted_decls ());
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
  Common.detect_sibling_module_inductive_collisions s;
  method_registry := Some
    ( match !global_method_registry with
    | Some reg -> reg
    | None -> Method_registry.create s );
  let analysis = Structure_analysis.analyze (get_method_registry ()) s in
  Hashtbl.clear global_inductive_names;
  List.iter
    (fun (name, mp) -> Hashtbl.replace global_inductive_names name mp)
    analysis.inductive_names;
  Hashtbl.clear global_scope_enum_table;
  List.iter
    (fun r -> Hashtbl.replace global_scope_enum_table r ())
    analysis.global_scope_enums;
  List.iter
    (fun (mi : Structure_analysis.module_info) ->
      match mi.wrapper_name with
      | Some name -> Hashtbl.replace wrapper_module_table mi.modpath name
      | None -> () )
    analysis.sorted_modules;
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
  let deferred_defs_acc = ref (mt ()) in
  let deferred_lifted_acc = ref (mt ()) in
  List.iter
    (fun ((mp, sel), wrapper_name) ->
      match wrapper_name with
      | Some name ->
        push_visible mp [];
        let func_sels = List.filter is_func_decl sel in
        let old_decls = !current_structure_decls in
        current_structure_decls := sel;
        let p_specs, p_defs, p_lifted =
          pp_wrapper_module_dual ~is_header ~wrapper_mp:mp name func_sels
        in
        current_structure_decls := old_decls;
        if not (Pp.ismt p_specs) then (
          Hashtbl.replace pending_wrapper_decls name p_specs;
          Hashtbl.replace unmerged_wrappers name () );
        if not (Pp.ismt p_defs) then
          deferred_defs_acc := !deferred_defs_acc ++ cut2 () ++ p_defs;
        if not (Pp.ismt p_lifted) then
          deferred_lifted_acc := !deferred_lifted_acc ++ cut2 () ++ p_lifted;
        pop_visible ()
      | None -> () )
    wrapper_names;
  let deferred_defs = !deferred_defs_acc in
  let deferred_lifted = !deferred_lifted_acc in
  name_cache :=
    Some
      (Name_resolution.create
         ~structure_analysis:analysis
         ~wrapper_modules:wrapper_module_table
         ~collision_wrappers:collision_wrapper_table
         ~global_scope_enums:global_scope_enum_table
         ~eponymous_records:global_eponymous_record_registry
         ~unmerged:unmerged_wrappers
         s );
  let ppl ((mp, sel), wrapper_name) =
    let old_decls = !current_structure_decls in
    current_structure_decls := sel;
    push_visible mp [];
    let p =
      match wrapper_name with
      | Some name ->
        let type_sels = List.filter (fun x -> not (is_func_decl x)) sel in
        let type_pp = prlist_sep_nonempty cut2 f type_sels in
        if Pp.ismt type_pp && is_header then
          match
            Hashtbl.find_opt pending_wrapper_decls name
          with
          | Some specs ->
            Hashtbl.remove pending_wrapper_decls name;
            str "struct "
            ++ str name
            ++ str " {"
            ++ fnl ()
            ++ specs
            ++ fnl ()
            ++ str "};"
          | None -> mt ()
        else begin
          (* Type aliases (Dtype) in type_sels are being rendered at global
             C++ scope (as [using T = ...] declarations, not inside any struct).
             Register them so [struct_qualifier_for] skips qualification in
             the .cpp file.  This fixes imported-module aliases like [cell]
             from [AliasSource.v] that appear at global scope in the header
             but would otherwise be incorrectly qualified as [AliasSource::cell]
             in the .cpp out-of-line function definitions. *)
          if is_header && not (Pp.ismt type_pp) then
            List.iter
              (fun (_, se) ->
                match se with
                | SEdecl (Dtype (r, _, _)) ->
                  Cpp_state.register_global_scope_type_alias r
                | _ -> () )
              type_sels;
          type_pp
        end
      | None ->
        let child_has_eponymous_ind child_name se =
          match se with
          | SEmodule m ->
            ( match m.ml_mod_expr with
            | MEstruct (_inner_mp, inner_sel) ->
              List.exists
                (fun (_l', se') ->
                  match se' with
                  | SEdecl (Dind (kn, ind)) ->
                    let found = ref false in
                    Array.iteri
                      (fun i _p ->
                        let ind_ref = GlobRef.IndRef (kn, i) in
                        let ind_name = Common.pp_global_name Type ind_ref in
                        let ind_name_cap = String.capitalize_ascii ind_name in
                        if String.equal ind_name_cap child_name then
                          found := true )
                      ind.ind_packets;
                    !found
                  | _ -> false )
                inner_sel
            | _ -> false )
          | _ -> false
        in
        let has_sibling_inductive child_name =
          List.exists
            (fun (_l', se') ->
              match se' with
              | SEdecl (Dind (kn, ind)) ->
                let found = ref false in
                Array.iteri
                  (fun i _p ->
                    let ind_ref = GlobRef.IndRef (kn, i) in
                    let ind_name = Common.pp_global_name Type ind_ref in
                    let ind_name_cap = String.capitalize_ascii ind_name in
                    if String.equal ind_name_cap child_name then
                      found := true )
                  ind.ind_packets;
                !found
              | _ -> false )
            sel
        in
        let has_child_collision =
          is_modfile mp
          && List.exists
               (fun (l, se) ->
                 match se with
                 | SEmodule _ ->
                   let child_name =
                     String.capitalize_ascii (Label.to_string l)
                   in
                   ( match
                       Hashtbl.find_opt global_inductive_names child_name
                     with
                   | Some ind_mp ->
                     let is_collision =
                       (not (ModPath.equal ind_mp mp))
                       && (not (child_has_eponymous_ind child_name se))
                       && not (has_sibling_inductive child_name)
                     in
                     is_collision
                   | None -> false )
                 | _ -> false )
               sel
        in
        if has_child_collision then (
          let parent_name = Table.escape_reserved_struct_name (String.capitalize_ascii (string_of_modfile mp)) in
          let is_colliding_child l se =
            let child_name = String.capitalize_ascii (Label.to_string l) in
            match Hashtbl.find_opt global_inductive_names child_name with
            | Some ind_mp ->
              (not (ModPath.equal ind_mp mp))
              && (not (child_has_eponymous_ind child_name se))
              && not (has_sibling_inductive child_name)
            | None -> false
          in
          let register_decl_modpaths qualified inner_sel =
            List.iter
              (fun (_l', se') ->
                match se' with
                | SEdecl (Dterm (r, _, _)) ->
                  let rmp = modpath_of_r r in
                  Hashtbl.replace wrapper_module_table rmp qualified;
                  Hashtbl.replace collision_wrapper_table rmp ()
                | SEdecl (Dfix (rn, _, _)) ->
                  Array.iter
                    (fun r ->
                      let rmp = modpath_of_r r in
                      Hashtbl.replace wrapper_module_table rmp qualified;
                      Hashtbl.replace collision_wrapper_table rmp () )
                    rn
                | _ -> () )
              inner_sel
          in
          List.iter
            (fun (l, se) ->
              match se with
              | SEmodule m when is_colliding_child l se ->
                let vis_mp = MPdot (mp, l) in
                Hashtbl.replace wrapper_module_table vis_mp parent_name;
                Hashtbl.replace collision_wrapper_table vis_mp ();
                ( match m.ml_mod_expr with
                | MEstruct (inner_mp, inner_sel) ->
                  Hashtbl.replace wrapper_module_table inner_mp parent_name;
                  Hashtbl.replace collision_wrapper_table inner_mp ();
                  register_decl_modpaths parent_name inner_sel
                | MEident alias_mp ->
                  Hashtbl.replace wrapper_module_table alias_mp parent_name;
                  Hashtbl.replace collision_wrapper_table alias_mp ()
                | _ -> () )
              | _ -> () )
            sel;
          if is_header then
            let non_colliding_pp, colliding_pp =
              with_render_ctx
                ~setup:(fun () -> render_ctx.rc_in_struct <- true)
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
          else
            let non_colliding_pp, colliding_pp =
              with_render_ctx
                ~setup:(fun () ->
                  render_ctx.rc_struct_name <- Some (str parent_name);
                  render_ctx.rc_struct_mp <- Some mp )
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
  let remaining_wrappers =
    if is_header then
      Hashtbl.fold
        (fun name specs acc ->
          let wrapper =
            str "struct "
            ++ str name
            ++ str " {"
            ++ fnl ()
            ++ specs
            ++ fnl ()
            ++ str "};"
          in
          acc ++ cut2 () ++ wrapper )
        pending_wrapper_decls
        (mt ())
    else
      mt ()
  in
  Hashtbl.clear pending_wrapper_decls;
  let pass2_lifted = Translation.take_lifted_decls () |> dedup_lifted_decls in
  let pass2_pre_pp, pass2_post_pp =
    if is_header then
      let main_module_name =
        match List.rev wrapper_names with
        | ((mp, _sel), None) :: _ ->
          Some (Table.escape_reserved_struct_name (String.capitalize_ascii (string_of_modfile mp)))
        | _ -> None
      in
      let rendered_lifted =
        List.map (fun d -> pp_cpp_decl (empty_env ()) d) pass2_lifted
      in
      let pre, post =
        List.partition
          (fun pp ->
            match main_module_name with
            | Some name ->
              not
                (Common.contains_substring
                   (Pp.string_of_ppcmds pp)
                   (name ^ "::") )
            | None -> false )
          rendered_lifted
      in
      let join lst = prlist_sep_nonempty cut2 (fun x -> x) lst in
      (join pre, join post)
    else
      (mt (), mt ())
  in
  let rev_rendered = List.rev rendered in
  let main_entry, pre_entries =
    match rev_rendered with
    | ((_, None), p) :: rest -> (Some p, List.rev rest)
    | _ -> (None, rendered)
  in
  let p_pre = prlist_sep_nonempty cut2 snd pre_entries in
  let p =
    match main_entry with
    | Some main_p ->
      prlist_sep_nonempty
        cut2
        (fun x -> x)
        (List.filter
           (fun x -> not (Pp.ismt x))
           [p_pre; remaining_wrappers; pass2_pre_pp; main_p] )
    | None ->
      if Pp.ismt remaining_wrappers then
        p_pre
      else if Pp.ismt p_pre then
        remaining_wrappers
      else
        p_pre ++ cut2 () ++ remaining_wrappers
  in
  if not (modular ()) then
    repeat (List.length wrapper_names) pop_visible ();
  (* Pop the initial visibility entries pushed at the top of this function. *)
  List.iter (fun _ -> pop_visible ()) initial_mps;
  v 0 (p ++ pass2_post_pp ++ deferred_lifted ++ deferred_defs) ++ fnl ()

(** Simple structure renderer without wrapper module handling. Used for
    signature rendering.

    @param f  Callback applied to each [(label, structure_elem)] pair to
              produce its pretty-printer document.
    @param s  Extraction structure (list of [(module_path, elem list)] pairs).
    @return Pretty-printer document for the rendered signature. *)
let do_struct f s =
  let ppl (mp, sel) =
    push_visible mp [];
    let p = prlist_sep_nonempty cut2 f sel in
    if modular () then pop_visible ();
    p
  in
  let p = prlist_sep_nonempty cut2 ppl s in
  if not (modular ()) then
    repeat (List.length s) pop_visible ();
  v 0 p ++ fnl ()

(** Main entry point: render structure to C++ implementation file. *)
let pp_struct s =
  do_struct_with_decl_tracking
    ~is_header:false
    (pp_structure_elem ~is_header:false pp_decl)
    s

(** Main entry point: render structure to C++ header file. *)
let pp_hstruct s =
  do_struct_with_decl_tracking
    ~is_header:true
    (pp_structure_elem ~is_header:true pp_hdecl)
    s

(** Render module signature (for .mli-style files, unused in current
    extraction). *)
let pp_signature s = do_struct pp_specif s

(** Language descriptor for C++ extraction. *)
let cpp_descr =
  {
    keywords;
    file_suffix = ".cpp";
    file_naming = file_of_modfile;
    preamble;
    pp_struct;
    pp_hstruct;
    sig_suffix = Some ".h";
    sig_preamble;
    pp_sig = pp_signature;
    pp_decl;
  }
