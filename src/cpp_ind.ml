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

(** Which C++ declarations a MiniML declaration becomes.

    This module contains:
    - ind_header_decls — inductive types
    - generate — what a MiniML declaration becomes, whichever file is being
      written; impl_decls / header_decls pick what the .cpp and the .h write

    Every entry point answers with declarations rather than with rendered
    text; {!pp_decls} is where they are printed. *)

open Util
open Names
open Table
open Miniml
open Common
open Minicpp
open Gen_decls
open Cpp_state
open Cpp_names

(** Declarations as generated, each with the name environment it is printed
    in. *)
type generated = (Common.env * Minicpp.cpp_decl) list

(** Declarations finished for the printer. *)
type rendered = (Common.env * Cpp_erasure.settled) list

(** [finished ds] finishes the declarations one MiniML declaration became. *)
let finished (ds : generated) : rendered =
  List.map (fun (env, d) -> (env, Cpp_pipeline.finish d)) ds


(** Print the declarations an entry point answered with. *)
let pp_decls (ds : rendered) =
  pp_list_stmt (fun (env, d) -> Cpp_print.pp_cpp_decl env d) ds

(** The struct a module's declarations are written inside of, when the module is
    written as a struct at all.

    An imported module's wrapper is recorded, because the name it is given is
    not always its own.  A module declared in the unit being extracted is not:
    it is emitted as a struct named after itself, and nothing records that,
    because nothing has to -- the visibility stack is still standing where its
    members are spelled.  Both kinds are emitted after every datatype, so a
    datatype's member naming either one is naming something still to come. *)
let module_struct_name (mp : ModPath.t) : string option =
  match Module_plan.wrapper_struct mp with
  | Some name -> Some name
  | None -> (
    match mp with
    | MPdot (_, lbl) -> Some (String.capitalize_ascii (Label.to_string lbl))
    | MPfile _ | MPbound _ -> None )

(** Finished declarations written later than they were generated, each group
    kept with the scope it was generated in and rendered in it. *)
type deferred = (Cpp_state.scope * rendered) list ref

let deferred name : deferred = Cpp_state.owned_list name

let defer (band : deferred) ds =
  if ds <> [] then band := (Cpp_state.current_scope (), ds) :: !band

let render_deferred (band : deferred) =
  let groups = List.rev !band in
  band := [];
  List.map (fun (sc, ds) -> Cpp_state.in_scope sc (fun () -> pp_decls ds)) groups

let discard (band : deferred) = band := []

(** Member definitions a datatype struct at namespace scope gave up because
    their bodies name a module's struct, which is emitted after every datatype
    and cannot be moved in front of one it holds by value. *)
let deferred_member_defs = deferred "deferred_member_defs"

(** The landing pads for erasure: file-scope [using X = std::any;] for a name
    with no C++ spelling behind it.  Written before everything, the concepts
    included, because an alias to [std::any] names nothing and the text that
    lands on it does not follow it. *)
let file_scope_erased_aliases = deferred "file_scope_erased_aliases"

(** The kinds of the template parameters of the inductive [kn]'s packets,
    as {!ind_header_decls} gives them. *)
let ind_template_kinds kn ind =
  match ind.ind_kind with
  | TypeClass _ | Record _ -> []
  | Standard | Coinductive ->
    List.filter_map
      (fun (i, p) ->
        let r = GlobRef.IndRef (kn, i) in
        if p.ip_logical || is_custom r || is_monad r then None
        else
          Some
            ( r,
              snd
                (Plan_templates.template_kinds r
                   (Common.ind_struct_tparams kn ind p)
                   (List.concat (Array.to_list p.ip_types)) ) ) )
      (List.mapi (fun i p -> (i, p)) (Array.to_list ind.ind_packets))

(* The same for a type alias [generate] writes: its kinds come out of its
   rendered right-hand side, and only the alias's own generation renders it. *)
let alias_template_kinds r l t =
  let written =
    match t with
    | Miniml.Tdummy Miniml.Ktype -> false
    | t ->
      not
        ( is_any_inline_custom r
        || Table.singleton_class_method r <> None
        || Ml_type_util.has_no_cpp_spelling
             (Translation.convert_ml_type_to_cpp_type (empty_env ()) l t) )
  in
  if written then [(r, type_alias_kinds r l t)] else []

let template_kinds struc =
  let kinds = ref [] in
  let decide l =
    List.iter (fun (r, k) -> Tparam_kinds.record r k) l;
    kinds := List.rev_append l !kinds
  in
  Modutil.struct_iter
    (function
      | Dind (kn, ind) -> decide (ind_template_kinds kn ind)
      | Dtype (r, l, t) -> decide (alias_template_kinds r l t)
      | _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  List.rev !kinds

(** What a declaration written in the header alone generates: its
    declarations; the member definitions that cross a cycle at namespace
    scope, written after the whole group ({!Member_hoist}); and, for an
    inductive promoted to its module's struct, whether that struct derives
    from [enable_shared_from_this]. *)
type header_generation = {
  decls : generated;
  member_defs : generated;
  promoted_sft : bool option;
}

let header_decls decls = {decls; member_defs = []; promoted_sft = None}

(** Render inductive type header (.h file).
    TypeClasses become C++ concepts, Records become structs,
    other inductives become variant-like structs with constructors.
    @param kn mutual inductive kernel name identifying the inductive block
    @param ind miniml representation of the mutual inductive type block
    @return pretty-printed C++ header fragment (forward declarations followed
            by full struct/concept/enum definitions), or [mt ()] when all
            packets in the block are custom or suppressed

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
let ind_header_decls kn ind =
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
    header_decls
      ( if (!render_ctx).rc_in_struct || (!render_ctx).rc_concepts_hoisted then []
        else [(empty_env (), gen_typeclass_cpp names.(0) fields)] )
  | Record fields ->
    (* Check if this is an eponymous record being merged into module struct *)
    let ind_ref = names.(0) in
    header_decls
      ( match !eponymous_record with
      | Some (epon_ref, _, _) when globref_equal ind_ref epon_ref ->
        [] (* Skip - merged into module struct *)
      | _ -> [(empty_env (), gen_record_cpp names.(0) fields ind.ind_packets.(0))] )
  | _ ->
    let is_mutual = Array.length ind.ind_packets > 1 in
    let forward_decls =
      if is_mutual then
        let rec fwd i =
          if i >= Array.length ind.ind_packets then
            []
          else
            let ip = (kn, i) in
            if is_custom (GlobRef.IndRef ip)
               || is_monad (GlobRef.IndRef ip) then
              fwd (i + 1)
            else
              let p = ind.ind_packets.(i) in
              (* Compute template parameters the same way as the full definition
                 (see param_vars below at the struct gen site). Parameters
                 (before the colon) become template params; indices (after the
                 colon) are erased. *)
              let param_vars = Common.ind_struct_tparams kn ind p in
              (* The forward declaration carries the same name and the same
                 template parameters as the full definition below; both are
                 built from [param_vars] and printed by the same node. *)
              let tparams =
                List.map (fun v -> (TTtypename, v)) param_vars
              in
              (empty_env (), Dstruct_fwd (tparams, names.(i))) :: fwd (i + 1)
        in
        fwd 0
      else
        []
    in
    (* Helper to find method candidates from current_structure_decls for a given
       inductive. IMPORTANT: Skip functions whose signatures reference type
       aliases (Dtype) from the same module. This prevents issues like
       `heap_delete_max : tree -> priqueue` becoming a method on `tree`, where
       `priqueue` is a type alias not visible from inside `tree`. *)
    let find_methods_for_inductive ind_ref =
      (* Enum inductives are rendered as [enum class] in C++, which cannot have
         member functions. Skip method registration entirely so that functions
         like [negb : bool -> bool] are not registered as methods of [Bool0],
         which would produce invalid [a0->negb()] or [this->negb()] calls. *)
      if Table.is_enum_inductive ind_ref then []
      else
      let ind_modpath = modpath_of_r ind_ref in
      let module_type_aliases =
        ref (Method_registry.collect_module_type_aliases
               ~extract_decl:(fun (_l, se) ->
                 match se with SEdecl d -> Some d | _ -> None)
               ind_modpath !current_structure_decls)
      in
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
                if globref_equal fwd_ref ind_ref then
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
          List.exists (globref_equal r) excluded_refs
          || List.exists refs_excluded args
        | Miniml.Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
        | Miniml.Tmeta {contents = Some t} -> refs_excluded t
        | _ -> false
      in
      (* Check if function comes from the same Rocq module as the inductive *)
      let same_module r = ModPath.equal (modpath_of_r r) ind_modpath in
      (* Collect the candidates first and keep only those the rule about
         calls keeps ([Method_registry.settle_file_calls]), as the registry's
         scan did. *)
      let eligible = ref [] in
      let consider r body ty =
        if
          same_module r
          && (not (refs_excluded ty))
          && Method_registry.would_register ind_ref body ty
        then eligible := (r, body, ty) :: !eligible
      in
      List.iter
        (fun (_l, se) ->
          match se with
          | SEdecl d ->
            List.iter
              (fun fd -> consider fd.fd_ref fd.fd_body fd.fd_type)
              (Mlutil.term_defs d)
          | _ -> () )
        !current_structure_decls;
      (* A call to a method of any type is rendered on its receiver, so only
         a callee that is a method of nothing is left for the rule. *)
      let already_method c =
        Method_registry.lookup (get_method_registry ()) c <> None
      in
      let calls =
        Method_registry.file_calls ind_modpath !current_structure_decls
      in
      let kept =
        Method_registry.settle_file_calls ~already_method
          ~calls:(fun (_, body, _) -> calls body)
          ~ref_of:(fun (r, _, _) -> r)
          (List.rev !eligible)
      in
      (* Newest first, as before. *)
      List.rev
        (List.filter_map
           (fun (r, body, ty) -> planned_method_candidate ind_ref r body ty)
           kept)
    in
    let promoted_sft = ref None in
    let rec pp i =
      if i >= Array.length ind.ind_packets then
        []
      else
        let ip = (kn, i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip)
           || is_monad (GlobRef.IndRef ip) then
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
                          globref_equal r ind_ref
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
              when globref_equal ind_ref epon_ref ->
              !method_candidates
            | _
              when (not (!render_ctx).rc_in_struct) && not is_inside_submodule_decl
              ->
              (* For top-level inductives only, find methods from sibling
                 declarations *)
              find_methods_for_inductive ind_ref
            | _ ->
              (* Inside a module, non-eponymous inductives: the registry
                 lookup below handles these with proper forward-ref
                 filtering. *)
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
                    (globref_equal r)
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
                          (globref_equal r)
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
          let param_vars = Common.ind_struct_tparams kn ind p in
          let mutual_partners =
            if is_mutual then
              let partners = ref [] in
              for j = Array.length ind.ind_packets - 1 downto 0 do
                if j <> i then begin
                  let pj = ind.ind_packets.(j) in
                  partners :=
                    (names.(j), cnames.(j), pj.ip_types,
                     pj.ip_consarg_names) :: !partners
                end
              done;
              !partners
            else []
          in
          let decl =
            gen_ind_header_v2
              ~is_mutual
              ~consarg_names:p.ip_consarg_names
              ~mutual_partners
              param_vars
              names.(i)
              cnames.(i)
              p.ip_types
              (List.rev methods)
              ind.ind_kind
            |> Plan_templates.deapply_plain_struct_tvars
          in
          (* Check if this inductive is being promoted into its module struct.
             When promoted, render fields flat (no wrapping struct) since the
             module struct provides the wrapper. *)
          let is_promoted =
            match !eponymous_promote_ref with
            | Some r -> globref_equal r names.(i)
            | None -> false
          in
          if is_promoted then
            (* A promoted inductive has no struct of its own: the module
               struct it was merged into is its wrapper, so it contributes
               members rather than a nested type. *)
            match decl with
            | Dstruct ds ->
              promoted_sft := Some ds.ds_needs_shared_from_this;
              (empty_env (), Dfields ds) :: pp (i + 1)
            | _ ->
              (* Non-Dstruct promoted inductive (shouldn't happen normally) *)
              (empty_env (), decl) :: pp (i + 1)
          else
            (* DESIGN: Contextual wrapping for inductive definitions - If inside
               a struct/module: generate the inductive directly (no namespace
               wrapper) - If at module scope: wrap in a namespace struct (which
               becomes a struct via Dnspace)

               This allows inductives to nest naturally inside modules while
               maintaining proper scoping at the module level. *)
            let wrapped_decl =
              match decl with
              | Denum _ -> decl (* Enums don't need namespace wrapper *)
              | _ ->
                if (!render_ctx).rc_in_struct then
                  decl
                else
                  Dnspace (Some names.(i), [decl])
            in
            (empty_env (), wrapped_decl) :: pp (i + 1)
    in
    let group = pp 0 in
    (* Inside a struct the cycle does not bite: a nested class's member bodies
       are only compiled once the enclosing class is complete, which is after
       every sibling has been written.  At namespace scope nothing defers
       them, so the members that cross the cycle are written after the whole
       group. *)
    let group, member_defs =
      if (!render_ctx).rc_in_struct then
        (group, [])
      else
        let group = if is_mutual then Member_hoist.split_group group else group in
        (* The other cycle a struct at namespace scope can be in, and the one
           its own layout says nothing about.  A function promoted to a method
           here may have come from a module, and its body may still call that
           module's other functions -- but a module's struct is emitted after
           every datatype, and cannot be moved in front of one it holds by
           value.  Only the body: out-lining leaves the signature where it
           was.

           Not the datatype's own home module, though.  Its wrapper is where
           the datatype itself was hoisted out of, so a member naming a
           sibling there is naming something already written -- and moving
           such a member out costs more than it buys, because the definition
           then has to repeat a return type that named the struct's own
           nested types in class scope. *)
        let home = MutInd.modpath kn in
        let own_nspace_names =
          Array.to_list
            (Array.map
               (fun r -> Some (String.capitalize_ascii (str_global Type r)))
               names )
        in
        let group, defs =
          Member_hoist.split_named ~body_only:true
            ~names:(fun r ->
              let mp = modpath_of_r r in
              (not (ModPath.equal mp home))
              && module_struct_name mp <> None
              (* A module path in the table says where the name was written in
                 Rocq, not which struct it ends up in: a function promoted onto
                 a datatype is emitted with that datatype, among the structs
                 this one is already sitting between.  Reaching for the modpath
                 to answer "which struct holds this" is the same mistake the
                 collision wrappers made, where registration and rendering
                 disagreed about where a declaration belonged; it is worth
                 distrusting the modpath here for the same reason. *)
              && is_registered_method r = None
              (* And not the struct this datatype is written inside of.  At
                 namespace scope the inductive is wrapped in a struct named
                 after itself, and a module of that same name is merged into
                 it -- so the callee is a sibling already above us, not a
                 struct still to come. *)
              && not (List.mem (module_struct_name mp) own_nspace_names) )
            group
        in
        (group, defs)
    in
    {decls = forward_decls @ group; member_defs; promoted_sft = !promoted_sft}

(** What a type class instance becomes: the struct carrying its methods, and
    the [static_assert] that checks the struct against the class's concept.

    An instance is named from wherever the class is used, and a concept check
    cannot be written for a struct that is still a template, so the assert is
    only worth emitting for a ground instance.  Both declarations go to
    namespace scope; an instance declared inside a module is lifted out of the
    module's struct rather than emitted as a member of it. *)
let finish_instance_struct = Plan_templates.deapply_plain_struct_tvars

let plan_instance_methods r a t =
  Gen_decls.plan_instance_methods ~finish:finish_instance_struct r a t

(* Each method of the struct of the instance [r] declared with the head its
   plan gives it, which was made before anything was generated; under
   [CRANE_CHECK_IR] the head it was generated with is checked against it. *)
let planned_methods r decl =
  let planned mf =
    if Probe.checking () then
      Callable_abi.check_instance_method ~instance:r mf.mf_name
        (Callable_abi.of_instance_method ~instance:r mf);
    let abi = Callable_abi.planned_instance_method ~instance:r mf.mf_name in
    match Callable_abi.receiver abi with
    | Some {params; ret; _} when List.length params = List.length mf.mf_params ->
      { mf with
        mf_tparams = Callable_abi.declared_head abi;
        mf_ret_type = ret;
        mf_params = List.map2 (fun (id, _) ty -> (id, ty)) mf.mf_params params }
    | Some _ | None ->
      CErrors.anomaly
        Pp.(str "the method " ++ Id.print mf.mf_name ++ str " of " ++ GlobRef.print r
            ++ str " is generated with other parameters than planned.")
  in
  let rec on_decl = function
    | Dstruct ds ->
      Dstruct
        { ds with
          ds_fields =
            List.map
              (function Fmethod mf, vis, tag -> (Fmethod (planned mf), vis, tag) | f -> f)
              ds.ds_fields }
    | Dtemplate (temps, c, d) -> Dtemplate (temps, c, on_decl d)
    | d -> d
  in
  on_decl decl

let instance_decls r a t =
  let ds_opt, class_ref_opt, concept_args =
    Gen_decls.gen_instance_struct r a t
  in
  let ds_opt = Option.map (fun d -> planned_methods r (finish_instance_struct d)) ds_opt in
  let struct_decl =
    match ds_opt with
    | Some ds -> [(empty_env (), ds)]
    | None -> []
  in
  let is_template =
    match ds_opt with
    | Some (Dtemplate _) -> true
    | Some (Dstruct {ds_tparams = _ :: _; _}) -> true
    | _ -> false
  in
  let static_assert_decl =
    match class_ref_opt with
    | Some class_ref when not is_template ->
      [ ( empty_env (),
          Dstatic_assert (CPPconcept_app (class_ref, r, concept_args), None) ) ]
    | _ -> []
  in
  struct_decl @ static_assert_decl

(** What one MiniML declaration generates, before the file being written
    picks what it writes. *)
type generation =
  | Functions of {
      funs : Gen_decls.generated_fun list;
      lifted : lifted_placement;
    }
  | Header_only of (unit -> header_generation)
      (** Written in the header alone, generated ahead of the files in the
          scope the header writes it in ({!header_entity}). *)
  | Instance of GlobRef.t * ml_ast * ml_type
      (** A type-class instance, written in the header alone and generated
          ahead of both files ({!instance_entity}). *)
  | Nothing

(** Where the helpers lifted out of generated functions are written. *)
and lifted_placement =
  | Inline  (** The header writes each function's helpers in front of it. *)
  | By_element of cpp_decl list
      (** The element places them, as a constant's or a function's are. *)
  | Unwritten  (** A fixpoint inside a template struct writes none. *)

(** Whether the module being written is one whose members the header
    defines in a class template ({!Scope_plan.templated}).  Asked of the
    plan, not of the render context: the implementation writes no template,
    and generates what the header does all the same. *)
let in_template () = Scope_plan.templated (top_visible_mp ())

(** [functions ~lifted funs], with every definition filed in the header
    inside a template struct, which has no implementation file. *)
let functions ~lifted (funs : Gen_decls.generated_fun list) =
  let in_header (g : Gen_decls.generated_fun) =
    match g.gf_entity with
    | Defined (d, _) -> {g with gf_entity = Defined (d, Header)}
    | Declared _ -> g
  in
  let funs = if in_template () then List.map in_header funs else funs in
  Functions {funs; lifted}

(** {2 Generating once}

    The functions generated at a declaration in a module are the same
    whichever file is being written: emission decides nothing the plan has
    not -- {!Extract_env} checks that no table grows -- and what a
    generation reads beyond its declaration and module is planned
    ({!in_template}, {!Common.freeze_global_ids}).  So every function is
    generated once, ahead of both files ({!generating_ahead}), and each
    file's pass takes it from here.  Under [CRANE_CHECK_IR] a pass
    translates it again anyway and checks the two agree. *)

module Node_table = Hashtbl.Make (struct
  type t = Obj.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

(** What was generated ahead of the files, by the MiniML node it was
    generated from, with the module it was generated in. *)
let generated : (ModPath.t * Gen_decls.generated_fun list) list Node_table.t =
  Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset generated)

let ahead = ref false

let generating_ahead f =
  ahead := true;
  Fun.protect ~finally:(fun () -> ahead := false) f

(* Set while what was generated ahead is generated again to check it
   ({!regenerating}): nothing is recorded or claimed. *)
let rechecking = ref false

let regenerating f =
  let outer = !rechecking in
  rechecking := true;
  Fun.protect ~finally:(fun () -> rechecking := outer) f

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let same_generation (a : Gen_decls.generated_fun) (b : Gen_decls.generated_fun) =
  compare a.gf_entity b.gf_entity = 0
  && List.equal Id.equal (fst a.gf_env) (fst b.gf_env)
  && Id.Set.equal (snd a.gf_env) (snd b.gf_env)

(** [ahead_once ~what ~recorded ~record ~same ?planned ?take gen] is
    [gen ()] ahead of the files ({!generating_ahead}), recorded ([record])
    with the module it is generated in, and handed to [planned] to plan what
    taking it will need.  A file's pass takes what was recorded
    ([recorded ()]) in the same module, handing it to [take] -- to claim the
    helpers lifted out of it, or record its entity -- unless it is only
    generating it again to check it ({!regenerating}); under
    [CRANE_CHECK_IR] it generates it again and compares the two with
    [same].  That nothing was recorded there is a walk ahead that missed a
    declaration a render reaches, an anomaly about [what].  While planning,
    it is [gen ()]. *)
let ahead_once ~what ~recorded ~record ~same ?(planned = ignore) ?(take = Fun.id) gen =
  match get_phase () with
  | Plan -> gen ()
  | Emit _ when !ahead && not !rechecking ->
    let v = gen () in
    record ((top_visible_mp (), v) :: recorded ());
    planned v;
    v
  | Emit _ -> (
    let mp = top_visible_mp () in
    match List.find_map (fun (mp', v) -> if ModPath.equal mp' mp then Some v else None) (recorded ()) with
    | Some v ->
      let taken = if !rechecking then v else take v in
      if Sys.getenv_opt "CRANE_CHECK_IR" <> None
         && not (same v (fst (Translation.collecting_lifted gen)))
      then
        CErrors.anomaly
          Pp.(str "Crane: " ++ what () ++ str " was generated differently ahead of the files and "
              ++ str (if !rechecking then "again in the reverse order." else "in one of them."));
      taken
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: " ++ what () ++ str " was reached while rendering in the module "
            ++ str (ModPath.to_string mp) ++ str " that was not generated ahead of the files there.") )

(** [in_node_table table node] is the [~recorded] and [~record] of
    {!ahead_once} for what is recorded in [table] by the physical node
    [node]. *)
let in_node_table table node =
  let key = Obj.repr node in
  ( (fun () -> Option.default [] (Node_table.find_opt table key)),
    fun l -> Node_table.replace table key l )

(** {2 Which element of the header places a lifted helper}

    A helper lifted out of several generations is placed by the first of
    them the header writes.  Which one that is is planned in the walk ahead
    of the files, which reaches the header's elements in the order the
    header writes them ({!plan_header_claim}), rather than claimed against
    the helpers the header has placed so far as it reaches them; under
    [CRANE_CHECK_IR] the header still claims them that way and must agree
    ({!header_claim}).  Only the header places an element's helpers. *)

(** The helpers some element of the header places, as planned so far. *)
let header_placed : GlobRef.t list ref = State.cell State.Unit []

(** The helpers each generation the header takes places, by the physical
    identity of the generation. *)
let header_claims : cpp_decl list Node_table.t = Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset header_claims)

(** [plan_header_claim key lifted] plans that the generation [key], whose
    bodies lifted [lifted], places those of them no earlier element of the
    header places. *)
let plan_header_claim key lifted =
  let placed_here d =
    match decl_globref d with
    | None -> true
    | Some r ->
      (not (List.exists (globref_equal r) !header_placed))
      && (header_placed := r :: !header_placed; true)
  in
  Node_table.replace header_claims (Obj.repr key) (List.filter placed_here lifted)

(** [header_claim key lifted] is what {!plan_header_claim} planned the
    generation [key] places of [lifted]. *)
let header_claim key lifted =
  match Node_table.find_opt header_claims (Obj.repr key) with
  | Some planned ->
    if Probe.checking () && get_phase () = Emit Intf then begin
      let claimed = Translation.claim_lifted lifted in
      if not (List.equal ( == ) planned claimed) then
        Probe.violation "header claims"
          Pp.(str "the header places other helpers at a generation than planned: "
              ++ prlist_with_sep (fun () -> str ", ")
                   (fun d -> Option.cata GlobRef.print (str "?") (decl_globref d))
                   claimed
              ++ str " where the plan says "
              ++ prlist_with_sep (fun () -> str ", ")
                   (fun d -> Option.cata GlobRef.print (str "?") (decl_globref d))
                   planned )
    end;
    planned
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: a generation was taken whose helpers' placement was not planned.")

(** [generated_once ?on_reuse node gen] is {!ahead_once} for the functions
    generated at the MiniML node [node]: a file's pass hands them to
    [on_reuse] to replay any effect generating them had. *)
let generated_once ?(on_reuse = ignore) ?planned node gen =
  let recorded, record = in_node_table generated node in
  ahead_once ~what:(fun () -> Pp.str "a function") ~recorded ~record
    ~same:(List.equal same_generation)
    ?planned
    ~take:(fun funs -> on_reuse funs; funs)
    gen

(** [generate d] is what the MiniML declaration [d] generates, for whichever
    file is being written: functions translated once, with their file
    recorded, or declarations only the header writes.  Inline customs,
    projections merged into a struct, and functions emitted as methods
    generate nothing. *)
let generate d =
  (* A method candidate is a registered method
     ({!Method_registry.planned_candidate}). *)
  let skipped r =
    is_eponymous_record_projection r
    || is_suppressed_projection r
    || is_registered_method r <> None
  in
  let group fds =
    match filter_dfix fds with
    | [] -> Nothing
    | fds ->
      functions
        ~lifted:(if in_template () then Unwritten else Inline)
        (generated_once d (fun () -> gen_dfuns_dual fds))
  in
  match d with
  | (Dtype (r, _, _) | Dterm (r, _, _)) when is_any_inline_custom r -> Nothing
  | Dterm (r, _, _) when skipped r -> Nothing
  | Dind (kn, ind) -> Header_only (fun () -> ind_header_decls kn ind)
  (* A singleton class is a concept, declared where concepts are. *)
  | Dtype (r, _, _) when Table.singleton_class_method r <> None ->
    if (!render_ctx).rc_in_struct || (!render_ctx).rc_concepts_hoisted then Nothing
    else
      Header_only
        (fun () ->
          header_decls
            [(empty_env (), gen_typeclass_cpp r (Table.get_record_field_bindings r))] )
  | Dtype (r, l, t) ->
    if t == Taxiom then begin
      Cpp_erasure.register_axiom_type r;
      Table.add_erased_type_const r
    end;
    ( match t with
    | Miniml.Tdummy Miniml.Ktype -> Nothing (* erased Type aliases *)
    | t
      when Ml_type_util.has_no_cpp_spelling
             (Translation.convert_ml_type_to_cpp_type (empty_env ()) l t) ->
      (* An abbreviation for a type that is not written in C++ is not written
         either, asked of the type as it would be printed: [Definition bigE :=
         ioE +' envE] is a [Sum1] of event families that have no C++ name, and
         would give [using bigE = Sum1<, >].  What names the abbreviation was
         for -- an event family -- is erased at every use, so nothing looks
         for it. *)
      Nothing
    | t -> Header_only (fun () -> header_decls [(empty_env (), gen_type_alias r l (Some t))]) )
  | Dterm (r, a, (Tglob (ty, _, _) as t)) when is_monad ty ->
    group [{fd_ref = r; fd_body = a; fd_type = t}]
  | Dterm (r, a, t) when is_typeclass_instance a t -> Instance (r, a, t)
  | Dterm (r, a, t) ->
    (* The helpers lifted out of the body are the element's to place: those
       no earlier element of the header places ({!plan_header_claim}). *)
    let gen () =
      let (gf_entity, gf_env), gf_lifted =
        Translation.collecting_lifted @@ fun () ->
        match gen_decl_for_pp r a t with
        | Some ds, env, tvars -> (Gen_decls.defined ds tvars, env)
        | None, _, _ when in_template () ->
          let ds, env, _ = gen_decl r a t in
          (Defined (ds, Header), env)
        | None, _, _ ->
          (* Not a function: a declaration, and no definition anywhere. *)
          let ds, env = gen_spec r a t in
          (Declared ds, env)
      in
      [{Gen_decls.gf_entity; gf_env; gf_lifted}]
    in
    let lifted funs = List.concat_map (fun g -> g.Gen_decls.gf_lifted) funs in
    let claimed = ref None in
    let reuse funs = claimed := Some (header_claim funs (lifted funs)) in
    let funs =
      generated_once ~planned:(fun funs -> plan_header_claim funs (lifted funs)) ~on_reuse:reuse d gen
    in
    let helpers =
      match !claimed with
      | Some helpers -> helpers
      | None -> List.concat_map (fun g -> g.Gen_decls.gf_lifted) funs
    in
    functions ~lifted:(By_element helpers) funs
  | Dfix fds -> group fds

(** [finished_ahead_once table key finish ~what] is [finish ()] ahead of
    the files ({!generating_ahead}), recorded in [table] by the physical
    identity of [key].  A file's pass takes it from there -- finished again
    and compared under [CRANE_CHECK_IR] -- and finds it missing only as an
    anomaly about [what]. *)
let finished_ahead_once table key finish ~what =
  let earlier = Node_table.find_opt table (Obj.repr key) in
  match (get_phase (), earlier) with
  | Plan, _ -> CErrors.anomaly Pp.(str "Crane: " ++ str what ++ str " was finished while planning.")
  | Emit _, Some f when !ahead ->
    if !rechecking && compare f (finish ()) <> 0 then
      CErrors.anomaly
        Pp.(str "Crane: " ++ str what ++ str " was finished differently again in the reverse order.");
    f
  | Emit _, None when !ahead ->
    let f = finish () in
    Node_table.replace table (Obj.repr key) f;
    f
  | Emit _, Some f ->
    if Sys.getenv_opt "CRANE_CHECK_IR" <> None && compare f (finish ()) <> 0 then
      CErrors.anomaly
        Pp.(str "Crane: " ++ str what
            ++ str " was finished differently ahead of the files and in one of them.");
    f
  | Emit _, None ->
    CErrors.anomaly
      Pp.(str "Crane: " ++ str what ++ str " was rendered that was not finished ahead of \
                                         the files.")

(** Each declaration finished on its own ahead of the files -- one written
    without a definition, a lifted helper -- by its physical identity. *)
let finished_alone_ahead : Cpp_erasure.settled Node_table.t = Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset finished_alone_ahead)

let finished_alone d =
  finished_ahead_once finished_alone_ahead d (fun () -> Cpp_pipeline.finish d) ~what:"a declaration"

(** [render_decl env d] prints [d] finished ahead of the files
    ({!finished_alone}). *)
let render_decl env d = Cpp_print.pp_cpp_decl env (finished_alone d)

(** Each root instance's declarations, finished as one group ahead of the
    files, by the physical identity of their generation. *)
let instances_finished_ahead : rendered Node_table.t = Node_table.create 16

let () = State.on_reset State.Unit (fun () -> Node_table.reset instances_finished_ahead)

let finished_instance (ds : generated) =
  finished_ahead_once instances_finished_ahead ds (fun () -> finished ds) ~what:"an instance"

(** The entity each generated definition was finalized as ahead of the
    files, by the physical identity of the declaration generated: a function
    filed in the header is a new record of the same declaration
    ({!functions}). *)
let finalized_ahead : Function_entity.t Node_table.t = Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset finalized_ahead)

(** [finalized funs] pairs each generated function with its entity, every
    definition among them finished as one group
    ({!Function_entity.finalize_group}); [None] for a declaration.  The
    functions are finished ahead of the files, with the walk that generates
    them ({!generating_ahead}), and a file's pass takes their entities from
    there, checked under [CRANE_CHECK_IR] like the generation itself; that it
    finds one missing is an anomaly. *)
let finalized (funs : Gen_decls.generated_fun list) =
  let finalize () =
    let entities =
      Function_entity.finalize_group
        (List.filter_map
           (fun (g : Gen_decls.generated_fun) ->
             match g.gf_entity with Defined (d, _) -> Some d | Declared _ -> None )
           funs )
    in
    let rec pair funs es =
      match (funs, es) with
      | ({Gen_decls.gf_entity = Defined _; _} as g) :: funs, e :: es ->
        (g, Some e) :: pair funs es
      | ({gf_entity = Declared _; _} as g) :: funs, es -> (g, None) :: pair funs es
      | [], [] -> []
      | _ -> assert false
    in
    pair funs entities
  in
  match get_phase () with
  | Plan -> CErrors.anomaly Pp.(str "Crane: a function was finished while planning.")
  | Emit _ when !ahead && !rechecking ->
    let paired = finalize () in
    List.iter
      (fun ((g : Gen_decls.generated_fun), e) ->
        match (g.gf_entity, e) with
        | Defined (d, _), Some e ->
          if
            not
              (Option.equal
                 (fun a b -> compare a b = 0)
                 (Node_table.find_opt finalized_ahead (Obj.repr d))
                 (Some e) )
          then
            CErrors.anomaly
              Pp.(str "Crane: a function was finished differently again in the reverse order.")
        | Declared d, _ -> ignore (finished_alone d : Cpp_erasure.settled)
        | Defined _, None -> () )
      paired;
    paired
  | Emit _ when !ahead ->
    let paired = finalize () in
    List.iter
      (fun ((g : Gen_decls.generated_fun), e) ->
        match (g.gf_entity, e) with
        | Defined (d, _), Some e -> Node_table.replace finalized_ahead (Obj.repr d) e
        | Declared d, _ -> ignore (finished_alone d : Cpp_erasure.settled)
        | Defined _, None -> () )
      paired;
    paired
  | Emit _ ->
    let paired =
      List.map
        (fun (g : Gen_decls.generated_fun) ->
          match g.gf_entity with
          | Declared _ -> (g, None)
          | Defined (d, _) -> (
            match Node_table.find_opt finalized_ahead (Obj.repr d) with
            | Some e -> (g, Some e)
            | None ->
              CErrors.anomaly
                Pp.(str "Crane: a function was rendered that was not finished ahead of the \
                         files.") ) )
        funs
    in
    if Sys.getenv_opt "CRANE_CHECK_IR" <> None
       && compare (List.map snd paired) (List.map snd (finalize ())) <> 0
    then
      CErrors.anomaly
        Pp.(str "Crane: a function was finished differently ahead of the files and in one \
                 of them.");
    paired

(** The views of [funs] a file writes, finished: a definition in the file
    that holds it, and in the header a declaration of a definition the
    implementation file holds. *)
let function_views ~is_header ~lifted_inline funs =
  let paired = finalized funs in
  (* Functions of one group the header defines may call one another, and at
     namespace scope a call is looked up where it is written: a struct sees
     its later members, a namespace does not, and an explicit template
     argument list -- [fmap<T1, T2>(f, fs)] -- rules out finding the callee
     by argument-dependent lookup at instantiation.  So the group is declared
     before its first definition. *)
  let in_header (g : Gen_decls.generated_fun) =
    match g.gf_entity with Defined (_, Header) -> true | _ -> false
  in
  let forward =
    is_header
    && (not (!render_ctx).rc_in_struct)
    && List.length (List.filter (fun (g, _) -> in_header g) paired) > 1
  in
  let declarations =
    if not forward then []
    else
      List.filter_map
        (fun ((g : Gen_decls.generated_fun), entity) ->
          match entity with
          | Some e when in_header g ->
            Some (g.gf_env, Function_entity.declaration e)
          | _ -> None )
        paired
  in
  declarations
  @ List.concat_map
    (fun ((g : Gen_decls.generated_fun), entity) ->
      let with_env d = (g.gf_env, d) in
      let lifted =
        if is_header && lifted_inline then
          List.map (fun d -> (empty_env (), finished_alone d)) g.gf_lifted
        else []
      in
      let views =
        match (g.gf_entity, entity) with
        | Defined (_, file), Some e ->
          ( match (file, is_header) with
          | Header, true ->
            [ with_env
                ( if forward then Function_entity.definition_after_declaration e
                  else Function_entity.definition e ) ]
          | Implementation, false ->
            (* The header declared it. *)
            [with_env (Function_entity.definition_after_declaration e)]
          | Implementation, true -> [with_env (Function_entity.declaration e)]
          | Header, false -> [] )
        | Declared d, _ ->
          if is_header then [with_env (finished_alone d)] else []
        | Defined _, None -> assert false
      in
      lifted @ views )
    paired

(** {2 The generated program}

    Every generation the printer is about to render is recorded as an entity
    of {!Generated_program}, and what the printer writes is read back from
    the recorded entity. *)

(** The source entity a MiniML declaration is: an inductive block by its
    first packet. *)
let decl_entity = function
  | Dind (kn, _) -> GlobRef.IndRef (kn, 0)
  | Dtype (r, _, _) | Dterm (r, _, _) -> r
  | Dfix fds -> (List.hd fds).fd_ref

(** [entity r decls helpers] is the generation of [r]: [decls], and the
    helpers among [helpers]. *)
let entity r decls helpers : Generated_program.entity =
  { entity_id = Entity_id.of_ref r;
    decls;
    helpers = List.filter_map Generated_program.helper helpers }

(** [record_entity r decls helpers] records the generation of [r]. *)
let record_entity r decls helpers = Generated_program.record (entity r decls helpers)

(** [funs_entities ~fallback funs] is each generated function as the entity
    its declaration is about, [fallback] where it says none. *)
let funs_entities ~fallback (funs : Gen_decls.generated_fun list) =
  List.map
    (fun (g : Gen_decls.generated_fun) ->
      let d = match g.gf_entity with Defined (d, _) | Declared d -> d in
      entity (Option.default fallback (decl_globref d)) [d] g.gf_lifted )
    funs

(** [record_funs ~fallback funs] records {!funs_entities}. *)
let record_funs ~fallback funs =
  List.iter (fun e -> ignore (Generated_program.record e)) (funs_entities ~fallback funs)


(** What a file writes for one MiniML declaration, and the helpers lifted
    out of it that the element places. *)
type element = {
  rendered : rendered;
  helpers : cpp_decl list;
}

(** What was generated ahead of the header for each instance, by the
    physical node of its body, with the module it was generated in: its
    declarations, and the helpers lifted out of its methods. *)
let instances_generated : (ModPath.t * (generated * cpp_decl list)) list Node_table.t =
  Node_table.create 16

let () = State.on_reset State.Unit (fun () -> Node_table.reset instances_generated)

let same_generated (a : generated) (b : generated) =
  List.equal
    (fun ((ids, avoid), d) ((ids', avoid'), d') ->
      List.equal Id.equal ids ids' && Id.Set.equal avoid avoid' && compare d d' = 0 )
    a b

(** [instance_entity r a t] is the instance [r], of body [a] and type [t],
    generated ({!instance_decls}) and recorded as the entity [r], with the
    helpers lifted out of its methods, which come before it.  It is
    generated ahead of the files, like a function ({!generated_once}), and
    taken from there by the header. *)
let instance_entity r a t =
  let recorded, record = in_node_table instances_generated a in
  ahead_once
    ~what:(fun () -> Pp.(str "the instance " ++ GlobRef.print r))
    ~recorded ~record
    ~same:(fun (ds, _) (ds', _) -> same_generated ds ds')
    ~planned:(fun ((_, lifted) as v) -> plan_header_claim v lifted)
    ~take:(fun ((ds, lifted) as v) ->
      let helpers = header_claim v lifted in
      ignore (record_entity r (List.map snd ds) helpers);
      (ds, helpers) )
    (fun () -> Translation.collecting_all_lifted (fun () -> instance_decls r a t))

(** {2 The header's scope of a module}

    How the header writes a module's body: inside a struct or not, and with
    the module's class concepts already declared ahead of its struct or not
    ({!Cpp.walk_as_rendered} works both out from the module's frame).  Planned
    for every module ahead of the files, by the module, and checked against
    the header's render context as it enters the module. *)

type header_scope = {
  in_struct : bool;
  concepts_hoisted : bool;
}

let header_scopes : header_scope MPmap.t ref = State.cell State.Unit MPmap.empty

let plan_header_scope mp scope = header_scopes := MPmap.add mp scope !header_scopes

let header_scope mp = MPmap.find_opt mp !header_scopes

(** The concept of each class, generated ahead of the files in the module
    declaring it, by the class. *)
let concepts_generated : (ModPath.t * cpp_decl) list Ref.User.Tbl.t = Ref.User.Tbl.create 16

let () = State.on_reset State.Unit (fun () -> Ref.User.Tbl.reset concepts_generated)

(** [concept r fields] is the concept of the class [r], of fields [fields]:
    generated ahead of the files ({!generating_ahead}) and taken from there
    by the header, which generates it again under [CRANE_CHECK_IR] to
    compare. *)
let concept r fields =
  ahead_once
    ~what:(fun () -> Pp.(str "the concept of " ++ GlobRef.print r))
    ~recorded:(fun () -> Option.default [] (Ref.User.Tbl.find_opt concepts_generated r))
    ~record:(Ref.User.Tbl.replace concepts_generated r)
    ~same:(fun d d' -> compare d d' = 0)
    (fun () -> Gen_decls.gen_typeclass_cpp r fields)

(** The methods of each eponymous record, generated ahead of the files with
    the helpers lifted out of them, by the record. *)
let record_methods_generated :
    (ModPath.t * ((cpp_field * cpp_visibility * section_tag) list * cpp_decl list)) list
    Ref.User.Tbl.t =
  Ref.User.Tbl.create 8

let () = State.on_reset State.Unit (fun () -> Ref.User.Tbl.reset record_methods_generated)

(** [record_methods r vars candidates] is the methods the eponymous record
    [r], of variables [vars], is given, made of [candidates], with the
    helpers lifted out of them: generated ahead of the files, and taken from
    there by the header ({!ahead_once}). *)
let record_methods r vars candidates =
  ahead_once
    ~what:(fun () -> Pp.(str "the methods of the record " ++ GlobRef.print r))
    ~recorded:(fun () -> Option.default [] (Ref.User.Tbl.find_opt record_methods_generated r))
    ~record:(Ref.User.Tbl.replace record_methods_generated r)
    ~same:(fun (fields, _) (fields', _) -> compare fields fields' = 0)
    ~planned:(fun ((_, lifted) as v) -> plan_header_claim v lifted)
    ~take:(fun ((fields, lifted) as v) -> (fields, header_claim v lifted))
    (fun () ->
      Translation.collecting_all_lifted (fun () -> Gen_decls.gen_record_methods r vars candidates) )

(** The methods of each eponymous record, finished ahead of the files, by
    the physical identity of their generation. *)
let record_methods_finished : Cpp_erasure.settled Node_table.t = Node_table.create 8

let () = State.on_reset State.Unit (fun () -> Node_table.reset record_methods_finished)

let finished_record_methods r vars fields =
  finished_ahead_once record_methods_finished fields
    (fun () ->
      Cpp_pipeline.finish
        (Dfields
           { ds_ref = r;
             ds_fields = fields;
             ds_tparams = List.map (fun v -> (TTtypename, v)) vars;
             ds_constraint = None;
             ds_needs_shared_from_this = false } ) )
    ~what:"an eponymous record's methods"

(** What was generated ahead of the header for each declaration it writes
    alone, by the declaration's physical node, with the module it was
    generated in: its generation, and the helpers lifted out of it. *)
let headers_generated : (ModPath.t * (header_generation * cpp_decl list)) list Node_table.t =
  Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset headers_generated)

let same_header_generation a b =
  same_generated a.decls b.decls
  && same_generated a.member_defs b.member_defs
  && a.promoted_sft = b.promoted_sft

(** [header_entity d gen] is what the declaration [d] generates for the
    header ([gen ()]), with the helpers lifted out of it, recorded as the
    entity [d] is.  It is generated ahead of the files, in the scope the
    header writes the module in ({!header_scope}), like an instance
    ({!instance_entity}), and taken from there by the header. *)
let header_entity d gen =
  let recorded, record = in_node_table headers_generated d in
  ahead_once
    ~what:(fun () -> GlobRef.print (decl_entity d))
    ~recorded ~record
    ~same:(fun (g, _) (g', _) -> same_header_generation g g')
    ~planned:(fun ((_, lifted) as v) -> plan_header_claim v lifted)
    ~take:(fun ((g, lifted) as v) ->
      let helpers = header_claim v lifted in
      ignore (record_entity (decl_entity d) (List.map snd g.decls) helpers);
      (g, helpers) )
    (fun () -> Translation.collecting_all_lifted gen)

(** What the header alone writes of each declaration, finished as one group
    ahead of the files, by the physical identity of its generation: the
    declarations, and apart from them the member definitions written after
    the group. *)
let headers_finished : rendered Node_table.t = Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset headers_finished)

let finished_header (ds : generated) =
  finished_ahead_once headers_finished ds (fun () -> finished ds) ~what:"a header declaration"

(** [in_header_scope f] runs [f] in the render context the header writes
    the current module's body in, as planned ({!header_scope}). *)
let in_header_scope f =
  let mp = top_visible_mp () in
  match header_scope mp with
  | Some {in_struct; concepts_hoisted} ->
    with_render_ctx
      (fun c -> {c with rc_in_struct = in_struct; rc_concepts_hoisted = concepts_hoisted})
      f
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the module " ++ str (ModPath.to_string mp) ++ str " has no planned header scope.")

(** What [d] generates, a declaration the header alone writes generated in
    the scope the header writes it in. *)
let generate_in_scope d k =
  match d with
  | Dind _ | Dtype _ -> in_header_scope (fun () -> k (generate d))
  | Dterm _ | Dfix _ -> k (generate d)

type ahead = {
  entities : Generated_program.entity list;
  functions : cpp_decl list;
  finish : unit -> unit;
  helpers : cpp_decl list;
}

let nothing_ahead = {entities = []; functions = []; finish = ignore; helpers = []}

let functions_ahead ~entities (funs : Gen_decls.generated_fun list) =
  { entities;
    functions =
      List.filter_map
        (fun (g : Gen_decls.generated_fun) ->
          match g.gf_entity with Defined (d, _) -> Some d | Declared _ -> None )
        funs;
    finish =
      (fun () -> ignore (finalized funs : (Gen_decls.generated_fun * Function_entity.t option) list));
    helpers = List.concat_map (fun (g : Gen_decls.generated_fun) -> g.gf_lifted) funs }

let generate_ahead d =
  generate_in_scope d @@ function
  | Functions {funs; _} -> functions_ahead ~entities:(funs_entities ~fallback:(decl_entity d) funs) funs
  | Instance (r, a, t) ->
    let ds, helpers = instance_entity r a t in
    { entities = [entity r (List.map snd ds) helpers];
      functions = [];
      finish = (fun () -> ignore (finished_instance ds : rendered));
      helpers }
  | Header_only gen ->
    let g, lifted = header_entity d gen in
    { nothing_ahead with
      entities = [entity (decl_entity d) (List.map snd g.decls) lifted];
      finish =
        (fun () ->
          ignore (finished_header g.member_defs : rendered);
          ignore (finished_header g.decls : rendered) ) }
  | Nothing -> nothing_ahead

let regenerate_ahead d =
  regenerating @@ fun () ->
  generate_in_scope d @@ function
  | Instance (r, a, t) -> ignore (instance_entity r a t : generated * cpp_decl list)
  | Header_only gen -> ignore (header_entity d gen : header_generation * cpp_decl list)
  | Functions _ | Nothing -> ()

let decls_for ~is_header d =
  match generate d with
  | Functions {funs; lifted} ->
    record_funs ~fallback:(decl_entity d) funs;
    let lifted_inline, helpers =
      match lifted with
      | Inline -> (true, [])
      | By_element helpers -> (false, helpers)
      | Unwritten -> (false, [])
    in
    { rendered = function_views ~is_header ~lifted_inline funs; helpers }
  | Header_only gen when is_header ->
    let g, helpers = header_entity d gen in
    defer deferred_member_defs (finished_header g.member_defs);
    Option.iter (fun sft -> eponymous_promote_sft := sft) g.promoted_sft;
    { rendered = finished_header g.decls; helpers }
  | Instance (r, a, t) when is_header ->
    let ds, helpers = instance_entity r a t in
    { rendered = finished_instance ds; helpers }
  | Header_only _ | Instance _ | Nothing -> { rendered = []; helpers = [] }

let impl_decls = decls_for ~is_header:false
let header_decls = decls_for ~is_header:true
