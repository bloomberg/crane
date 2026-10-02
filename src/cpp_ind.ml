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

(** [finished ds] finishes the declarations one MiniML declaration became, as
    one group ({!Cpp_pipeline.finish_group}): a fixpoint's functions may call
    one another. *)
let finished (ds : generated) : rendered =
  let envs, decls = List.split ds in
  List.combine envs (Cpp_pipeline.finish_group decls)

let render_decl env d = Cpp_print.pp_cpp_decl env (Cpp_pipeline.finish d)

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
  match wrapper_struct mp with
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
    if (!render_ctx).rc_in_struct || (!render_ctx).rc_concepts_hoisted then
      []
    else
      [(empty_env (), gen_typeclass_cpp names.(0) fields ind.ind_packets.(0))]
  | Record fields ->
    (* Check if this is an eponymous record being merged into module struct *)
    let ind_ref = names.(0) in
    ( match !eponymous_record with
    | Some (epon_ref, _, _)
      when globref_equal ind_ref epon_ref ->
      [] (* Skip - merged into module struct *)
    | _ -> [(empty_env (), gen_record_cpp names.(0) fields ind.ind_packets.(0))]
    )
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
      (* Collect the candidates first and register only those the rule about
         calls keeps ([Method_registry.settle_file_calls]).  Registering is a
         side effect: a function registered but then not rendered as a method
         would be called with method syntax that nothing defines. *)
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
          | SEdecl (Dterm (r, body, ty)) -> consider r body ty
          | SEdecl (Dfix (rv, defs, typs)) ->
            Array.iteri (fun i r -> consider r defs.(i) typs.(i)) rv
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
           (fun (r, body, ty) -> try_register_method ind_ref r body ty)
           kept)
    in
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
                  param_vars
                  ret_ml
              in
              (* Check if the return type is erased (Tany or unnamed Tvar) *)
              if Translation.type_is_erased ret_cpp then
                register_method_returns_any r )
            methods;
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
            |> Gen_decls.deapply_plain_struct_tvars
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
              eponymous_promote_sft := ds.ds_needs_shared_from_this;
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
    let group =
      if (!render_ctx).rc_in_struct then
        group
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
        defer deferred_member_defs (finished defs);
        group
    in
    forward_decls @ group

(** What a type class instance becomes: the struct carrying its methods, and
    the [static_assert] that checks the struct against the class's concept.

    An instance is named from wherever the class is used, and a concept check
    cannot be written for a struct that is still a template, so the assert is
    only worth emitting for a ground instance.  Both declarations go to
    namespace scope; an instance declared inside a module is lifted out of the
    module's struct rather than emitted as a member of it. *)
let instance_decls r a t =
  let ds_opt, class_ref_opt, concept_args =
    Gen_decls.gen_instance_struct r a t
  in
  let ds_opt = Option.map Gen_decls.deapply_plain_struct_tvars ds_opt in
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
      lifted_inline : bool;
          (** Whether the header writes the helpers lifted out of each
              function in front of it.  A constant's or function's stay
              queued instead, for the element's own placement; a fixpoint
              inside a template struct writes none. *)
    }
  | Header_only of (unit -> generated)
      (** Written in the header alone, and generated only for it: generating
          an inductive's header defers member definitions as it goes. *)
  | Nothing

(** [functions ~lifted_inline funs], with every definition filed in the
    header inside a template struct, which has no implementation file. *)
let functions ~lifted_inline (funs : Gen_decls.generated_fun list) =
  let in_header (g : Gen_decls.generated_fun) =
    match g.gf_entity with
    | Defined (d, _) -> {g with gf_entity = Defined (d, Header)}
    | Declared _ -> g
  in
  let funs =
    if (!render_ctx).rc_in_template then List.map in_header funs else funs
  in
  Functions {funs; lifted_inline}

(** {2 Generating once}

    After discovery, emission decides nothing -- {!Extract_env} checks that no
    table grows -- so functions the implementation pass generated are what the
    header pass would generate at the same declaration in the same context.
    The header pass takes them from here instead of translating the bodies
    again.  Under [CRANE_CHECK_IR] it translates them anyway and checks the
    two agree. *)

module Node_table = Hashtbl.Make (struct
  type t = Obj.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

(** What the implementation pass generated, by the MiniML node it generated
    it from, with the context it generated it in. *)
let generated_in_impl :
    (render_ctx * ModPath.t * Gen_decls.generated_fun list) list Node_table.t =
  Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset generated_in_impl)

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let same_generation (a : Gen_decls.generated_fun) (b : Gen_decls.generated_fun) =
  compare a.gf_entity b.gf_entity = 0
  && List.equal Id.equal (fst a.gf_env) (fst b.gf_env)
  && Id.Set.equal (snd a.gf_env) (snd b.gf_env)

(** [generated_once ?on_reuse node gen] is [gen ()], except that the header
    pass reuses what the implementation pass generated from the physical
    MiniML node [node] in the same render context and module, handing it to
    [on_reuse] to replay any effect generating it had. *)
let generated_once ?(on_reuse = ignore) node gen =
  let key = Obj.repr node in
  let rc = !render_ctx and mp = top_visible_mp () in
  let earlier = Option.default [] (Node_table.find_opt generated_in_impl key) in
  match get_phase () with
  | Emit Impl ->
    let funs = gen () in
    Node_table.replace generated_in_impl key ((rc, mp, funs) :: earlier);
    funs
  | Emit Intf -> (
    match
      List.find_map
        (fun (rc', mp', funs) ->
          if rc' = rc && ModPath.equal mp' mp then Some funs else None )
        earlier
    with
    | Some funs ->
      on_reuse funs;
      if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
        let again, _ = Translation.collecting_lifted gen in
        if not (List.equal same_generation funs again) then
          CErrors.anomaly
            Pp.(str "Crane: the header pass generated differently from the \
                     implementation pass.")
      end;
      funs
    | None -> gen () )
  | Discover -> gen ()

(** [generate d] is what the MiniML declaration [d] generates, for whichever
    file is being written: functions translated once, with their file
    recorded, or declarations only the header writes.  Inline customs,
    projections merged into a struct, and functions emitted as methods
    generate nothing. *)
let generate d =
  let skipped r =
    is_eponymous_record_projection r
    || is_suppressed_projection r
    || List.exists (fun (r', _, _, _) -> globref_equal r r') !method_candidates
    || is_registered_method r <> None
  in
  let group (rv, defs, typs) =
    let rv, defs, typs = filter_dfix rv defs typs in
    if Array.length rv = 0 then Nothing
    else
      functions
        ~lifted_inline:(not (!render_ctx).rc_in_template)
        (generated_once d (fun () -> gen_dfuns_dual (rv, defs, typs)))
  in
  match d with
  | (Dtype (r, _, _) | Dterm (r, _, _)) when is_any_inline_custom r -> Nothing
  | Dterm (r, _, _) when skipped r -> Nothing
  | Dind (kn, ind) -> Header_only (fun () -> ind_header_decls kn ind)
  | Dtype (r, l, t) ->
    if t == Taxiom then begin
      Cpp_erasure.register_axiom_type r;
      Table.add_erased_type_const r
    end;
    ( match t with
    | Miniml.Tdummy Miniml.Ktype -> Nothing (* erased Type aliases *)
    | t when Ml_type_util.ml_type_has_no_spelling t ->
      (* An abbreviation for a type that is not written in C++ is not written
         either: [Definition E2 := (FailE +' FailE)%type] would otherwise give
         a [using E2 = ;].  What names the abbreviation was for -- an event
         family -- is erased at every use, so nothing looks for it. *)
      Nothing
    | t -> Header_only (fun () -> [(empty_env (), gen_type_alias r l (Some t))]) )
  | Dterm (r, a, (Tglob (ty, _, _) as t)) when is_monad ty -> group ([|r|], [|a|], [|t|])
  | Dterm (r, a, t) when is_typeclass_instance a t ->
    Header_only (fun () -> instance_decls r a t)
  | Dterm (r, a, t) ->
    (* The helpers lifted out of the body stay queued, for the element's own
       placement; reusing the generation queues them again. *)
    let gen () =
      let (gf_entity, gf_env), gf_lifted =
        Translation.observing_lifted @@ fun () ->
        match gen_decl_for_pp r a t with
        | Some ds, env, tvars -> (Gen_decls.defined ds tvars, env)
        | None, _, _ when (!render_ctx).rc_in_template ->
          let ds, env, _ = gen_decl r a t in
          (Defined (ds, Header), env)
        | None, _, _ ->
          (* Not a function: a declaration, and no definition anywhere. *)
          let ds, env = gen_spec r a t in
          (Declared ds, env)
      in
      [{Gen_decls.gf_entity; gf_env; gf_lifted}]
    in
    let reuse funs =
      Translation.relift (List.concat_map (fun g -> g.Gen_decls.gf_lifted) funs)
    in
    functions ~lifted_inline:false (generated_once ~on_reuse:reuse d gen)
  | Dfix (rv, defs, typs) -> group (rv, defs, typs)

(** The entity the implementation pass finalized for each generated
    function, by physical identity: a generation the header pass reused
    ({!generated_once}) is finished once too. *)
let finalized_in_impl : Function_entity.t option Node_table.t =
  Node_table.create 64

let () = State.on_reset State.Unit (fun () -> Node_table.reset finalized_in_impl)

(** [finalized funs] pairs each generated function with its entity, every
    definition among them finished as one group
    ({!Function_entity.finalize_group}); [None] for a declaration.  The
    header pass takes the implementation pass's entities for functions it
    reused, checked under [CRANE_CHECK_IR] like the generation itself. *)
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
  let earlier g = Node_table.find_opt finalized_in_impl (Obj.repr g) in
  match get_phase () with
  | Emit Impl ->
    let paired = finalize () in
    List.iter (fun (g, e) -> Node_table.replace finalized_in_impl (Obj.repr g) e) paired;
    paired
  | Emit Intf when funs <> [] && List.for_all (fun g -> earlier g <> None) funs ->
    let paired = List.map (fun g -> (g, Option.get (earlier g))) funs in
    if Sys.getenv_opt "CRANE_CHECK_IR" <> None
       && compare (List.map snd paired) (List.map snd (finalize ())) <> 0
    then
      CErrors.anomaly
        Pp.(str "Crane: the header pass finished differently from the \
                 implementation pass.");
    paired
  | _ -> finalize ()

(** The views of [funs] a file writes, finished: a definition in the file
    that holds it, and in the header a declaration of a definition the
    implementation file holds. *)
let function_views ~is_header ~lifted_inline funs =
  List.concat_map
    (fun ((g : Gen_decls.generated_fun), entity) ->
      let with_env d = (g.gf_env, d) in
      let lifted =
        if is_header && lifted_inline then
          List.map (fun d -> (empty_env (), Cpp_pipeline.finish d)) g.gf_lifted
        else []
      in
      let views =
        match (g.gf_entity, entity) with
        | Defined (_, file), Some e ->
          ( match (file, is_header) with
          | Header, true | Implementation, false ->
            [with_env (Function_entity.definition e)]
          | Implementation, true -> [with_env (Function_entity.declaration e)]
          | Header, false -> [] )
        | Declared d, _ ->
          if is_header then [with_env (Cpp_pipeline.finish d)] else []
        | Defined _, None -> assert false
      in
      lifted @ views )
    (finalized funs)

let decls_for ~is_header d =
  match generate d with
  | Functions {funs; lifted_inline} -> function_views ~is_header ~lifted_inline funs
  | Header_only ds -> if is_header then finished (ds ()) else []
  | Nothing -> []

let impl_decls = decls_for ~is_header:false
let header_decls = decls_for ~is_header:true
