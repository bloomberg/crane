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

(** Inductive type rendering and declaration-level dispatch functions.

    This module contains:
    - pp_cpp_ind / pp_cpp_ind_header — rendering inductive types to C++
    - pp_decl / pp_hdecl / pp_hdecl_spec_only — dispatch for .cpp / .h /
      spec-only
    - pp_spec — printing module signatures
    - pp_tydef — type alias definitions *)

open Pp
open Util
open Names
open Table
open Miniml
open Modutil
open Common
open Minicpp
open Translation
open Cpp_state
open Cpp_names
open Cpp_print

(** Render inductive type implementation (.cpp file). Records and TypeClasses
    have no .cpp body. Enums are skipped as well. *)
let pp_cpp_ind kn ind =
  let names = Array.mapi (fun i p -> GlobRef.IndRef (kn, i)) ind.ind_packets in
  let cnames =
    Array.mapi
      (fun i p ->
        Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn, i), j + 1)) p.ip_types )
      ind.ind_packets
  in
  match ind.ind_kind with
  | Record fields | TypeClass fields -> mt ()
  | _ ->
    let rec pp i =
      if i >= Array.length ind.ind_packets then
        mt ()
      else
        let ip = (kn, i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip) then
          pp (i + 1)
        else if is_enum_cached (GlobRef.IndRef ip) then
          pp (i + 1) (* Enums have no .cpp body *)
        else
          (* Compute parameter-only type vars (same as in pp_cpp_ind_header) *)
          let param_sign = List.firstn ind.ind_nparams p.ip_sign in
          let num_param_vars =
            List.length (List.filter (fun x -> x == Miniml.Keep) param_sign)
          in
          let param_vars =
            List.map Common.tparam_name (List.firstn num_param_vars p.ip_vars)
          in
          pp_cpp_decl
            (empty_env ())
            (gen_ind_cpp param_vars names.(i) cnames.(i) p.ip_types)
          ++ pp (i + 1)
    in
    pp 0

(** Render a type alias definition (using declaration).
    @param ids list of type parameter identifiers
    @param name rendered name for the type
    @param def rendered definition (e.g., "= std::vector<int>") *)
let pp_tydef ids name def =
  let templates =
    match ids with
    | [] -> mt ()
    | _ ->
      str "template <"
      ++ List.fold_left
           (fun s v -> s ++ v)
           (mt ())
           (List.mapi
              (fun i v ->
                if i = 0 then
                  str "typename " ++ Id.print v
                else
                  str ", typename " ++ Id.print v )
              ids )
      ++ str "> "
  in
  hov 2 (templates ++ str "using " ++ name ++ def ++ str ";")

(** Dispatch for .cpp file rendering. Filters out inline customs, eponymous
    record projections, suppressed projections, method candidates, registered
    methods, and typeclass instances. *)
let pp_decl = function
  | Dtype (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_eponymous_record_projection r ->
    (* Skip - this is a projection for an eponymous record merged into module
       struct *)
    mt ()
  | Dterm (r, _, _) when is_suppressed_projection r -> mt ()
  | Dind (kn, i) -> mt () (* Inductives are fully defined in headers *)
  | Dtype (r, l, t) -> mt ()
  | Dterm (r, a, Tglob (ty, args, e)) when is_monad ty ->
    let defs =
      List.filter
        (fun (_, _, l) -> l == [])
        (gen_dfuns
           ( Array.of_list [r],
             Array.of_list [a],
             Array.of_list [Miniml.Tglob (ty, args, e)] ) )
    in
    pp_list_stmt (fun (ds, env, _) -> pp_cpp_decl env ds) defs
  | Dterm (r, _, _)
    when List.exists
           (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r')
           !method_candidates ->
    (* Skip - this function is generated as a method on the eponymous type *)
    mt ()
  | Dterm (r, _, _) when is_registered_method r <> None ->
    (* Skip - this function is registered as a method in another module *)
    mt ()
  | Dterm (r, a, t) when is_typeclass_instance a t ->
    (* Type class instances: fully defined in header, skip in implementation *)
    mt ()
  | Dterm (r, a, t) ->
    let ds, env, tvars = gen_decl_for_pp r a t in
    ( match (ds, tvars) with
    | Some ds, [] -> pp_cpp_decl env ds
    | _, _ -> mt () )
  | Dfix (rv, defs, typs) ->
    let rv, defs, typs = filter_dfix rv defs typs in
    if Array.length rv = 0 then
      mt ()
    else
      let defs =
        List.filter (fun (_, _, l) -> l == []) (gen_dfuns (rv, defs, typs))
      in
      pp_list_stmt (fun (ds, env, _) -> pp_cpp_decl env ds) defs

(** Render inductive type header (.h file).
    TypeClasses become C++ concepts, Records become structs,
    other inductives become variant-like structs with constructors.

    DESIGN: Mutual inductive support with forward declarations
    Rocq supports mutually recursive inductive types. In C++, this requires:
    1. Forward declarations so each struct can reference the others
    2. Full definitions immediately after

    Non-parameterized example:
      struct Tree;  // forward decl
      struct Node;  // forward decl
      struct Tree { ... Node usage ... };
      struct Node { ... Tree usage ... };

    Parameterized example (tree A / forest A):
      template <typename A> struct tree;    // forward decl
      template <typename A> struct forest;  // forward decl
      template <typename A> struct tree { ... forest<A> usage ... };
      template <typename A> struct forest { ... tree<A> usage ... };

    The forward declaration must carry the same template parameters as the
    full definition; a plain [struct tree;] followed by
    [template <typename A> struct tree { ... }] is a C++ error
    ("redefinition as different kind of symbol"). *)
let pp_cpp_ind_header kn ind =
  let names = Array.mapi (fun i p -> GlobRef.IndRef (kn, i)) ind.ind_packets in
  let cnames =
    Array.mapi
      (fun i p ->
        Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn, i), j + 1)) p.ip_types )
      ind.ind_packets
  in
  match ind.ind_kind with
  | TypeClass fields ->
    (* Type classes become C++ concepts *)
    (* Skip if concepts have been hoisted or we're inside a struct *)
    if render_ctx.rc_in_struct || render_ctx.rc_concepts_hoisted then
      mt ()
    else
      pp_cpp_decl
        (empty_env ())
        (gen_typeclass_cpp names.(0) fields ind.ind_packets.(0))
  | Record fields ->
    (* Check if this is an eponymous record being merged into module struct *)
    let ind_ref = names.(0) in
    ( match !eponymous_record with
    | Some (epon_ref, _, _)
      when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
      mt () (* Skip - merged into module struct *)
    | _ ->
      pp_cpp_decl
        (empty_env ())
        (gen_record_cpp names.(0) fields ind.ind_packets.(0)) )
  | _ ->
    let is_mutual = Array.length ind.ind_packets > 1 in
    let forward_decls =
      if is_mutual then
        let rec fwd i =
          if i >= Array.length ind.ind_packets then
            mt ()
          else
            let ip = (kn, i) in
            if is_custom (GlobRef.IndRef ip) then
              fwd (i + 1)
            else
              let p = ind.ind_packets.(i) in
              (* Compute template parameters the same way as the full definition
                 (see param_vars below at the struct gen site). Parameters
                 (before the colon) become template params; indices (after the
                 colon) are erased. *)
              let param_sign = List.firstn ind.ind_nparams p.ip_sign in
              let num_param_vars =
                List.length (List.filter (fun x -> x == Miniml.Keep) param_sign)
              in
              let param_vars =
                List.map
                  Common.tparam_name
                  (List.firstn num_param_vars p.ip_vars)
              in
              (* Use the same name as the struct definition (see Dstruct
                 printing below) so forward declarations match their
                 definitions. *)
              let name = pp_global Type names.(i) in
              let tmpl =
                match param_vars with
                | [] -> mt ()
                | vars ->
                  str "template <"
                  ++ prlist_with_sep
                       (fun () -> str ", ")
                       (fun v -> str "typename " ++ Id.print v)
                       vars
                  ++ str "> "
              in
              tmpl ++ str "struct " ++ name ++ str ";" ++ fnl () ++ fwd (i + 1)
        in
        fwd 0
      else
        mt ()
    in
    (* Helper to find method candidates from current_structure_decls for a given
       inductive. IMPORTANT: Skip functions whose signatures reference type
       aliases (Dtype) from the same module. This prevents issues like
       `heap_delete_max : tree -> priqueue` becoming a method on `tree`, where
       `priqueue` is a type alias not visible from inside `tree`. *)
    let find_methods_for_inductive ind_ref =
      let ind_modpath = modpath_of_r ind_ref in
      (* First, collect all type aliases (Dtype) defined in the same module.
         These are types like `priqueue := list tree` that become `using`
         declarations. Methods on nested inductives can't reference these
         (visibility issue). *)
      let module_type_aliases = ref [] in
      List.iter
        (fun (_l, se) ->
          match se with
          | SEdecl (Dtype (r, _, _))
            when ModPath.equal (modpath_of_r r) ind_modpath ->
            module_type_aliases := r :: !module_type_aliases
          | _ -> () )
        !current_structure_decls;
      (* Collect all inductives that come AFTER ind_ref in declaration order.
         Methods that reference these would cause forward declaration issues
         since the method body pattern-matches on variants that aren't defined
         yet. *)
      let forward_inductives = ref [] in
      let seen_current = ref false in
      List.iter
        (fun (_l, se) ->
          match se with
          | SEdecl (Dind (fwd_kn, fwd_ind)) ->
            Array.iteri
              (fun j _p ->
                let fwd_ref = GlobRef.IndRef (fwd_kn, j) in
                if Environ.QGlobRef.equal Environ.empty_env fwd_ref ind_ref then
                  seen_current := true
                else if !seen_current then
                  forward_inductives := fwd_ref :: !forward_inductives )
              fwd_ind.ind_packets
          | _ -> () )
        !current_structure_decls;
      (* Check if a type references any of the excluded references (type aliases
         or forward inductives) *)
      let excluded_refs = !module_type_aliases @ !forward_inductives in
      let rec refs_excluded ty =
        match ty with
        | Miniml.Tglob (r, args, _) ->
          List.exists (Environ.QGlobRef.equal Environ.empty_env r) excluded_refs
          || List.exists refs_excluded args
        | Miniml.Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
        | Miniml.Tmeta {contents = Some t} -> refs_excluded t
        | _ -> false
      in
      (* Check if function comes from the same Rocq module as the inductive *)
      let same_module r = ModPath.equal (modpath_of_r r) ind_modpath in
      let methods = ref [] in
      List.iter
        (fun (_l, se) ->
          match se with
          | SEdecl (Dterm (r, body, ty)) ->
            (* Skip if function signature references an excluded type (alias or
               forward inductive) *)
            if
              same_module r
              && (not (refs_excluded ty))
              && Method_registry.body_safe_for_method body
            then (
              match
                Method_registry.find_epon_arg_pos ind_ref ty
              with
              | Some (pos, ind_tvar_positions) ->
                methods := (r, body, ty, pos) :: !methods;
                register_method r ind_ref pos ~ind_tvar_positions ();
                Method_registry.add_candidate
                  (get_method_registry ())
                  ind_ref
                  (r, body, ty, pos)
              | None -> () )
          | SEdecl (Dfix (rv, defs, typs)) ->
            Array.iteri
              (fun i r ->
                let ty = typs.(i) in
                (* Skip if function signature references an excluded type (alias
                   or forward inductive) *)
                if
                  same_module r
                  && (not (refs_excluded ty))
                  && Method_registry.body_safe_for_method defs.(i)
                then
                  let body = defs.(i) in
                  match Method_registry.find_epon_arg_pos ind_ref ty with
                  | Some (pos, ind_tvar_positions) ->
                    methods := (r, body, ty, pos) :: !methods;
                    register_method r ind_ref pos ~ind_tvar_positions ();
                    Method_registry.add_candidate
                      (get_method_registry ())
                      ind_ref
                      (r, body, ty, pos)
                  | None -> () )
              rv
          | _ -> () )
        !current_structure_decls;
      !methods
    in
    let rec pp i =
      if i >= Array.length ind.ind_packets then
        mt ()
      else
        let ip = (kn, i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip) then
          pp (i + 1)
        else
          (* Get method candidates: first check if set via SEmodule processing,
             otherwise find from sibling declarations in
             current_structure_decls. IMPORTANT: Only use
             find_methods_for_inductive for top-level inductives. For inductives
             nested inside modules, only the eponymous type gets methods. This
             prevents issues like tree inside Priqueue getting methods that
             return priqueue (a sibling type alias not visible from inside
             tree). *)
          let ind_ref = GlobRef.IndRef ip in
          (* Check if ind_ref appears inside any SEmodule in
             current_structure_decls. This detects when an inductive is declared
             inside a submodule. *)
          let is_inside_submodule_decl =
            let rec find_in_module_expr = function
              | MEstruct (_, sel') ->
                List.exists
                  (fun (_l', se') ->
                    match se' with
                    | SEdecl (Dind (kn', ind')) ->
                      let rec check_packets i' =
                        if i' >= Array.length ind'.ind_packets then
                          false
                        else
                          let r = GlobRef.IndRef (kn', i') in
                          Environ.QGlobRef.equal Environ.empty_env r ind_ref
                          || check_packets (i' + 1)
                      in
                      check_packets 0
                    | _ -> false )
                  sel'
              | MEfunctor (_, _, me) -> find_in_module_expr me
              | MEapply (me, _) -> find_in_module_expr me
              | MEident _ -> false
            in
            List.exists
              (fun (_l, se) ->
                match se with
                | SEmodule m -> find_in_module_expr m.ml_mod_expr
                | _ -> false )
              !current_structure_decls
          in
          let methods =
            match !eponymous_type_ref with
            | Some epon_ref
              when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
              !method_candidates
            | _
              when (not render_ctx.rc_in_struct) && not is_inside_submodule_decl
              ->
              (* For top-level inductives only, find methods from sibling
                 declarations *)
              find_methods_for_inductive ind_ref
            | _ ->
              (* Inside a module, non-eponymous inductives don't get methods *)
              []
          in
          (* Also include method candidates from the registry (e.g., Nat::add
             from Corelib.Init.Nat for nat defined in Corelib.Init.Datatypes).
             Deduplicate: skip any that are already in the methods list. Filter
             out methods whose type references forward inductives to avoid
             forward reference errors in C++. *)
          let methods =
            let reg_candidates =
              Method_registry.get_candidates (get_method_registry ()) ind_ref
            in
            if reg_candidates = [] then
              methods
            else
              (* Compute forward inductives relative to this inductive. Use the
                 current structure decls to find inductives defined after this
                 one. *)
              let fwd_inds = ref [] in
              let seen_self = ref false in
              let decl_source = !current_structure_decls in
              List.iter
                (fun (_l, se) ->
                  match se with
                  | SEdecl (Dind (fwd_kn, fwd_ind)) ->
                    Array.iteri
                      (fun j _p ->
                        let fwd_ref = GlobRef.IndRef (fwd_kn, j) in
                        if
                          Environ.QGlobRef.equal
                            Environ.empty_env
                            fwd_ref
                            ind_ref
                        then
                          seen_self := true
                        else if !seen_self then
                          fwd_inds := fwd_ref :: !fwd_inds )
                      fwd_ind.ind_packets
                  | _ -> () )
                decl_source;
              let fwd_refs = !fwd_inds in
              let rec candidate_refs_fwd ty =
                match ty with
                | Miniml.Tglob (r, args, _) ->
                  List.exists
                    (Environ.QGlobRef.equal Environ.empty_env r)
                    fwd_refs
                  || List.exists candidate_refs_fwd args
                | Miniml.Tarr (t1, t2) ->
                  candidate_refs_fwd t1 || candidate_refs_fwd t2
                | Miniml.Tmeta {contents = Some t} -> candidate_refs_fwd t
                | _ -> false
              in
              let existing = List.map (fun (r, _, _, _) -> r) methods in
              let new_methods =
                List.filter
                  (fun (r, _, ty, _) ->
                    (not
                       (List.exists
                          (Environ.QGlobRef.equal Environ.empty_env r)
                          existing ) )
                    && not (candidate_refs_fwd ty) )
                  reg_candidates
              in
              methods @ new_methods
          in
          (* Compute parameter-only type vars. Parameters (before the colon)
             become template params. Indices (after the colon) are erased.
             ind.ind_nparams gives the number of Rocq parameters. p.ip_sign
             covers all args (params + indices). Count Keep entries in the first
             nparams positions to get param type var count. *)
          let param_sign = List.firstn ind.ind_nparams p.ip_sign in
          let num_param_vars =
            List.length (List.filter (fun x -> x == Miniml.Keep) param_sign)
          in
          let param_vars =
            List.map Common.tparam_name (List.firstn num_param_vars p.ip_vars)
          in
          (* Register methods that return std::any (for indexed inductives). A
             method returns std::any if its ML return type becomes an unnamed
             Tvar (indicating type erasure) after C++ conversion. *)
          List.iter
            (fun (r, _body, ty, _pos) ->
              (* Get return type from ML type *)
              let rec get_return_type = function
                | Miniml.Tarr (_, t2) -> get_return_type t2
                | ret -> ret
              in
              let ret_ml = get_return_type ty in
              (* Convert to C++ type with param_vars as template params *)
              let ret_cpp =
                Translation.convert_ml_type_to_cpp_type
                  (empty_env ())
                  Refset'.empty
                  param_vars
                  ret_ml
              in
              (* Check if the return type is erased (Tany or unnamed Tvar) *)
              if Translation.type_is_erased ret_cpp then
                register_method_returns_any r )
            methods;
          let decl =
            gen_ind_header_v2
              ~is_mutual
              param_vars
              names.(i)
              cnames.(i)
              p.ip_types
              (List.rev methods)
              ind.ind_kind
          in
          (* DESIGN: Contextual wrapping for inductive definitions - If inside a
             struct/module: generate the inductive directly (no namespace
             wrapper) - If at module scope: wrap in a namespace struct (which
             becomes a struct via Dnspace)

             This allows inductives to nest naturally inside modules while
             maintaining proper scoping at the module level. *)
          let wrapped_decl =
            match decl with
            | Denum _ -> decl (* Enums don't need namespace wrapper *)
            | _ ->
              if render_ctx.rc_in_struct then
                decl
              else
                Dnspace (Some names.(i), [decl])
          in
          pp_cpp_decl (empty_env ()) wrapped_decl ++ pp (i + 1)
    in
    forward_decls ++ pp 0

(** Dispatch for .h file rendering. Similar to pp_decl but generates header
    declarations instead of implementations. For template functions, generates
    full definitions inline (required by C++). For non-template functions,
    generates forward declarations. *)
let pp_hdecl = function
  | Dtype (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_eponymous_record_projection r ->
    (* Skip - this is a projection for an eponymous record merged into module
       struct *)
    mt ()
  | Dterm (r, _, _) when is_suppressed_projection r -> mt ()
  | Dind (kn, i) -> pp_cpp_ind_header kn i
  | Dtype (_, _, Miniml.Tdummy Miniml.Ktype) ->
    mt () (* Skip erased Type aliases *)
  | Dtype (r, l, t) ->
    let name = pp_global Type r in
    let l = rename_tvars keywords l in
    let ids, def =
      match find_type_custom_opt r with
      | Some (ids, s) -> (pp_string_parameters ids, str " =" ++ spc () ++ str s)
      | None ->
        ( pp_parameters l,
          if t == Taxiom then
            str " = std::any /* AXIOM TO BE REALIZED */"
          else
            str " =" ++ spc () ++ pp_type false l t )
    in
    pp_tydef l name def
  | Dterm (r, a, Tglob (ty, args, e)) when is_monad ty ->
    let defs =
      gen_dfuns_header
        ( Array.of_list [r],
          Array.of_list [a],
          Array.of_list [Miniml.Tglob (ty, args, e)] )
    in
    pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) defs
  | Dterm (r, _, _)
    when List.exists
           (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r')
           !method_candidates ->
    (* Skip - this function will be generated as a method on the eponymous
       type *)
    mt ()
  | Dterm (r, _, _) when is_registered_method r <> None ->
    (* Skip - this function is registered as a method in another module *)
    mt ()
  | Dterm (r, a, t) when is_typeclass_instance a t ->
    (* Type class instances: generate struct with static methods and
       static_assert *)
    let ds_opt, class_ref_opt, type_args =
      Translation.gen_instance_struct r a t
    in
    let struct_pp =
      match ds_opt with
      | Some ds -> pp_cpp_decl (empty_env ()) ds
      | None -> mt ()
    in
    (* Generate static_assert to verify the instance satisfies the concept. Skip
       for template instances (Dtemplate or Dstruct with tparams) — we can't
       instantiate a concept check without concrete types. *)
    let is_template =
      match ds_opt with
      | Some (Dtemplate _) -> true
      | Some (Dstruct {ds_tparams = _ :: _; _}) -> true
      | _ -> false
    in
    let static_assert_pp =
      match class_ref_opt with
      | Some class_ref when not is_template ->
        let instance_name = pp_global Type r in
        let class_name = pp_global Type class_ref in
        let type_args_pp =
          match type_args with
          | [] -> mt ()
          | args ->
            str ", "
            ++ prlist_with_sep
                 (fun () -> str ", ")
                 (fun ty ->
                   pp_cpp_type
                     false
                     []
                     (convert_ml_type_to_cpp_type
                        (empty_env ())
                        Refset'.empty
                        []
                        ty ) )
                 args
        in
        fnl ()
        ++ str "static_assert("
        ++ class_name
        ++ str "<"
        ++ instance_name
        ++ type_args_pp
        ++ str ">);"
      | _ -> mt ()
    in
    struct_pp ++ static_assert_pp
  | Dterm (r, a, t) ->
    let ds, env, tvars = gen_decl_for_pp r a t in
    ( match (ds, tvars) with
    | Some ds, [] ->
      (* For template structs, use full definitions instead of specs *)
      if render_ctx.rc_in_template then
        let ds, env, _ = gen_decl r a t in
        pp_cpp_decl env ds
      else
        (* Use decl_to_spec on the result from gen_decl_for_pp to produce a
           forward declaration. This correctly handles axiom values (Dfundef ->
           Dfundecl). *)
        pp_cpp_decl env (decl_to_spec ds)
    | Some ds, _ :: _ -> pp_cpp_decl env ds
    | None, _ ->
      if render_ctx.rc_in_template then
        let ds, env, _ = gen_decl r a t in
        pp_cpp_decl env ds
      else
        let ds, env = gen_spec r a t in
        pp_cpp_decl env ds )
  | Dfix (rv, defs, typs) ->
    let rv, defs, typs = filter_dfix rv defs typs in
    if Array.length rv = 0 then
      mt ()
    else if
      (* For template structs, generate full definitions inline, not just
         declarations *)
      render_ctx.rc_in_template
    then
      pp_list_stmt
        (fun (ds, env, _) -> pp_cpp_decl env ds)
        (gen_dfuns (rv, defs, typs))
    else
      pp_list_stmt
        (fun (ds, env) -> pp_cpp_decl env ds)
        (gen_dfuns_header (rv, defs, typs))

(** Like pp_hdecl but always generates forward declarations (specs), even for
    template functions. Used for wrapper struct injection into Dnspace structs
    where the full definitions are emitted later to avoid forward reference
    issues. *)
let pp_hdecl_spec_only = function
  | Dtype (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_any_inline_custom r -> mt ()
  | Dterm (r, _, _) when is_eponymous_record_projection r -> mt ()
  | Dterm (r, _, _) when is_suppressed_projection r -> mt ()
  | Dind (kn, i) -> pp_cpp_ind_header kn i
  | Dtype (_, _, Miniml.Tdummy Miniml.Ktype) ->
    mt () (* Skip erased Type aliases *)
  | Dtype (r, l, t) ->
    let name = pp_global Type r in
    let l = rename_tvars keywords l in
    let ids, def =
      match find_type_custom_opt r with
      | Some (ids, s) -> (pp_string_parameters ids, str " =" ++ spc () ++ str s)
      | None ->
        ( pp_parameters l,
          if t == Taxiom then
            str " = std::any /* AXIOM TO BE REALIZED */"
          else
            str " =" ++ spc () ++ pp_type false l t )
    in
    pp_tydef l name def
  | Dterm (r, _, _)
    when List.exists
           (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r')
           !method_candidates -> mt ()
  | Dterm (r, _, _) when is_registered_method r <> None -> mt ()
  | Dterm (r, a, Tglob (ty, args, e)) when is_monad ty ->
    mt () (* skip monadic for spec *)
  | Dterm (r, a, t) when is_typeclass_instance a t ->
    mt () (* skip typeclasses for spec *)
  | Dterm (r, a, t) ->
    (* Use gen_decl_for_pp to get the same signature as the full definition,
       then convert to a spec. This ensures forward declarations match
       out-of-line definitions, including concept-constrained template
       params. *)
    let ds, env, tvars = gen_decl_for_pp r a t in
    ( match (ds, tvars) with
    | Some ds, _ :: _ -> pp_cpp_decl env (Translation.decl_to_spec ds)
    | Some ds, [] -> pp_cpp_decl env (Translation.decl_to_spec ds)
    | None, _ ->
      let ds, env = gen_spec r a t in
      pp_cpp_decl env ds )
  | Dfix (rv, defs, typs) ->
    let rv, defs, typs = filter_dfix rv defs typs in
    if Array.length rv = 0 then
      mt ()
    else
      (* Generate specs derived from the full definition signatures
         (gen_dfuns_spec) to ensure forward declarations match the out-of-line
         definitions, including concept-constrained template parameters. *)
      pp_list_stmt
        (fun (ds, env) -> pp_cpp_decl env ds)
        (gen_dfuns_spec (rv, defs, typs))

(** Render a module signature element (spec). Module signatures become C++
    concepts (for module types) or struct declarations. *)
let pp_spec = function
  | Sval (r, _, _) when is_inline_custom r -> mt ()
  | Stype (r, _, _) when is_inline_custom r -> mt ()
  | Sind (kn, i) -> pp_cpp_ind_header kn i
  | Sval (r, b, t) ->
    let ds, env = gen_spec r b t in
    pp_cpp_decl env ds
  | Stype (_, _, Some (Miniml.Tdummy Miniml.Ktype)) ->
    mt () (* Skip erased Type aliases *)
  | Stype (r, vl, ot) ->
    let name = pp_global_name Type r in
    let l = rename_tvars keywords vl in
    let ids, def =
      match find_type_custom_opt r with
      | Some (ids, s) -> (pp_string_parameters ids, str " =" ++ spc () ++ str s)
      | None ->
        let ids = pp_parameters l in
        ( match ot with
        | None -> (ids, mt ())
        | Some Taxiom -> (ids, str " = std::any /* AXIOM TO BE REALIZED */")
        | Some t -> (ids, str " =" ++ spc () ++ pp_type false l t) )
    in
    pp_tydef l name def
