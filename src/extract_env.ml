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

open Miniml
open Constr
open Declarations
open Names
open ModPath
open Libnames
open Pp
open CErrors
open Util
open Table
open Extraction
open Modutil
open Common

(****************************************)
(** {1 Part I: computing Rocq environment} *)
(****************************************)

(** Returns the current toplevel environment as a (module_path, structure) pair
    with the structure reversed for bottom-up processing. *)
let toplevel_env () =
  let mp, struc = Safe_typing.flatten_env (Global.safe_env ()) in
  (mp, List.rev struc)

(** Returns all loaded library environments up to (and including) [dir_opt].
    If [dir_opt] is [None], includes the toplevel environment as well. *)
let environment_until dir_opt =
  let rec parse = function
    | [] when Option.is_empty dir_opt -> [toplevel_env ()]
    | [] -> []
    | d :: l ->
      let meb =
        Modops.destr_nofunctor
          (MPfile d)
          (Global.lookup_module (MPfile d)).mod_type
      in
      ( match dir_opt with
      | Some d' when DirPath.equal d d' -> [(MPfile d, meb)]
      | _ -> (MPfile d, meb) :: parse l )
  in
  parse (Library.loaded_libraries ())

(** {2 Visit: a structure recording the needed dependencies for the current
    extraction} *)

module type VISIT = sig
  (* Reset the dependencies by emptying the visit lists *)
  val reset : unit -> unit

  (* Add the module_path and all its prefixes to the mp visit list. We'll keep
     all fields of these modules. *)
  val add_mp_all : ModPath.t -> unit

  (* Add reference / ... in the visit lists. These functions silently add the mp
     of their arg in the mp list *)
  val add_ref : GlobRef.t -> unit

  val add_kn : KerName.t -> unit

  val add_decl_deps : ml_decl -> unit

  val add_spec_deps : ml_spec -> unit

  (* Test functions: is a particular object a needed dependency for the current
     extraction ? *)
  val needed_ind : MutInd.t -> bool

  val needed_cst : Constant.t -> bool

  val needed_mp : ModPath.t -> bool

  val needed_mp_all : ModPath.t -> bool
end

(** Visit module: dependency visitor that determines what to extract. Tracks
    which constants, inductives, and module paths are needed. *)
module Visit : VISIT = struct
  type must_visit = {
    mutable kn : KNset.t;
    mutable mp : MPset.t;
    mutable mp_all : MPset.t;
  }

  (* the imperative internal visit lists *)
  let v = {kn = KNset.empty; mp = MPset.empty; mp_all = MPset.empty}

  (* the accessor functions *)
  let reset () =
    v.kn <- KNset.empty;
    v.mp <- MPset.empty;
    v.mp_all <- MPset.empty

  let needed_ind i = KNset.mem (MutInd.user i) v.kn

  let needed_cst c = KNset.mem (Constant.user c) v.kn

  let needed_mp mp = MPset.mem mp v.mp || MPset.mem mp v.mp_all

  let needed_mp_all mp = MPset.mem mp v.mp_all

  let add_mp mp =
    check_loaded_modfile mp;
    v.mp <- MPset.union (prefixes_mp mp) v.mp

  let add_mp_all mp =
    check_loaded_modfile mp;
    v.mp <- MPset.union (prefixes_mp mp) v.mp;
    v.mp_all <- MPset.add mp v.mp_all

  let add_kn kn =
    v.kn <- KNset.add kn v.kn;
    add_mp (KerName.modpath kn)

  let add_ref =
    let open GlobRef in
    function
      | ConstRef c -> add_kn (Constant.user c)
      | IndRef (ind, _) | ConstructRef ((ind, _), _) -> add_kn (MutInd.user ind)
      | VarRef _ -> assert false

  (* Prune numeral-converter applications (e.g. [Nat.of_num_uint (...)]): the
     translation pass folds them into raw integer literals, so the converter,
     its digit-chain argument, and everything they transitively reference are
     never emitted.  Visiting them anyway would pull in the vestigial
     [of_num_uint]/[of_uint]/[Uint] machinery that no generated code calls. *)
  let add_decl_deps d =
    decl_iter_references
      ~prune:Translation.is_foldable_numeral_converter_app
      add_ref add_ref add_ref d

  let add_spec_deps = spec_iter_references add_ref add_ref add_ref
end

(** Computes which declarations are accessible from a module field. Adds
    constants, inductives, and submodules to the visit list. *)
let add_field_label mp = function
  | lab, (SFBconst _ | SFBmind _ | SFBrules _) ->
    Visit.add_kn (KerName.make mp lab)
  | lab, (SFBmodule _ | SFBmodtype _) -> Visit.add_mp_all (MPdot (mp, lab))

let rec add_labels mp = function
  | MoreFunctor (_, _, m) -> add_labels mp m
  | NoFunctor sign -> List.iter (add_field_label mp) sign

exception Impossible

(** Raises [Impossible] if the constant's type is an arity (type scheme). *)
let check_arity env cb =
  let t = cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let get_body lbody = EConstr.of_constr lbody

(** Checks if a constant body is a (co)fixpoint at index [i]. Returns
    [(is_fix, recd)] or raises [Impossible]. *)
let check_fix env sg cb i =
  match cb.const_body with
  | Def lbody ->
    ( match EConstr.kind sg (get_body lbody) with
    | Fix ((_, j), recd) when Int.equal i j ->
      check_arity env cb;
      (true, recd)
    | CoFix (j, recd) when Int.equal i j ->
      check_arity env cb;
      (false, recd)
    | _ -> raise Impossible )
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> raise Impossible

(** Tests equality of two mutual fixpoint declarations (names, bodies,
    types). *)
let prec_declaration_equal sg (na1, ca1, ta1) (na2, ca2, ta2) =
  Array.equal
    (Context.eq_annot Name.equal (EConstr.ERelevance.equal sg))
    na1
    na2
  && Array.equal (EConstr.eq_constr sg) ca1 ca2
  && Array.equal (EConstr.eq_constr sg) ta1 ta2

(** Groups consecutive structure fields that form a mutual (co)fixpoint into
    a single definition with shared bodies. Returns [(labels, is_fix, recd,
    remaining_struc)]. *)
let factor_fix env sg l cb msb =
  let ((is_fix, recd) as check) = check_fix env sg cb 0 in
  let n =
    Array.length
      (let fi, _, _ = recd in
       fi )
  in
  if Int.equal n 1 then
    ([|l|], is_fix, recd, msb)
  else (
    if List.length msb < n - 1 then raise Impossible;
    let msb', msb'' = List.chop (n - 1) msb in
    let labels = Array.make n l in
    List.iteri
      (fun j -> function
        | l, SFBconst cb' ->
          let check' = check_fix env sg cb' (j + 1) in
          if
            not
              ( (fst check : bool) == fst check'
              && prec_declaration_equal sg (snd check) (snd check') )
          then
            raise Impossible;
          labels.(j + 1) <- l
        | _ -> raise Impossible )
      msb';
    (labels, is_fix, recd, msb'') )

(** Expanding a [module_alg_expr] into a version without abbreviations or
    functor applications. This is done via a detour to entries (hack proposed by
    Elie) *)

let vm_state =
  (* VM bytecode is not needed here *)
  let vm_handler _ _ _ () = ((), None) in
  ((), {Mod_typing.vm_handler})

(** Expands a module algebraic expression into its structure and delta resolver
    by type-checking it. *)
let expand_mexpr env mp me =
  let inl = Some (Flags.get_inline_level ()) in
  let state =
    ( (Environ.universes env, Univ.Constraints.empty),
      Reductionops.inferred_universes )
  in
  let mb, (_, cst), _ =
    Mod_typing.translate_module state vm_state env mp inl (MExpr ([], me, None))
  in
  (mb.mod_type, mb.mod_delta)

(** Expands a module type algebraic expression into a full module type body. *)
let expand_modtype env mp me =
  let inl = Some (Flags.get_inline_level ()) in
  let state =
    ( (Environ.universes env, Univ.Constraints.empty),
      Reductionops.inferred_universes )
  in
  let mtb, _cst, _ =
    Mod_typing.translate_modtype state vm_state env mp inl ([], me)
  in
  mtb

let no_delta = Mod_subst.empty_delta_resolver

(** Flattens a module type into its structure and delta resolver, using a
    precomputed structure if available, otherwise expanding the algebraic
    expression. *)
let flatten_modtype env mp me_alg struc_opt =
  match struc_opt with
  | Some me -> (me, no_delta)
  | None ->
    let mtb = expand_modtype env mp me_alg in
    (mtb.mod_type, mtb.mod_delta)

(** Ad-hoc update of environment, inspired by [Mod_typing.check_with_aux_def].
*)

(** Builds a local environment for a [with Definition] clause by adding all
    structure fields before the targeted definition. *)
let env_for_mtb_with_def env mp me reso idl =
  let struc = Modops.destr_nofunctor mp me in
  let l = Label.of_id (List.hd idl) in
  let spot = function
    | l', SFBconst _ -> Label.equal l l'
    | _ -> false
  in
  let before = fst (List.split_when spot struc) in
  Modops.add_structure mp before reso env

(** Resolves a label to a constant through a delta resolver. *)
let make_cst resolver mp l =
  Mod_subst.constant_of_delta_kn resolver (KerName.make mp l)

(** Resolves a label to a mutual inductive through a delta resolver. *)
let make_mind resolver mp l =
  Mod_subst.mind_of_delta_kn resolver (KerName.make mp l)

(* From a [structure_body] (i.e. a list of [structure_field_body]) to
   specifications. *)

let rec extract_structure_spec env mp reso = function
  | [] -> []
  | (l, SFBconst cb) :: msig ->
    let c = make_cst reso mp l in
    let s = extract_constant_spec env c cb in
    let specs = extract_structure_spec env mp reso msig in
    if logical_spec s then
      specs
    else (
      Visit.add_spec_deps s;
      (l, Spec s) :: specs )
  | (l, SFBmind _) :: msig ->
    let mind = make_mind reso mp l in
    let s = Sind (mind, extract_inductive env mind) in
    let specs = extract_structure_spec env mp reso msig in
    if logical_spec s then
      specs
    else (
      Visit.add_spec_deps s;
      (l, Spec s) :: specs )
  | (l, SFBrules _) :: msig ->
    let specs = extract_structure_spec env mp reso msig in
    specs
  | (l, SFBmodule mb) :: msig ->
    let specs = extract_structure_spec env mp reso msig in
    let spec = extract_mbody_spec env mb.mod_mp mb in
    (l, Smodule spec) :: specs
  | (l, SFBmodtype mtb) :: msig ->
    let specs = extract_structure_spec env mp reso msig in
    let spec = extract_mbody_spec env mtb.mod_mp mtb in
    (l, Smodtype spec) :: specs

(* From [module_expression] to specifications *)

(* Invariant: the [me_alg] given to [extract_mexpr_spec] and
   [extract_mexpression_spec] should come from a [mod_type_alg] field. This way,
   any encountered [MEident] should be a true module type. *)

and extract_mexpr_spec env mp1 (me_struct_o, me_alg) =
  match me_alg with
  | MEident mp ->
    Visit.add_mp_all mp;
    MTident mp
  | MEwith (me', WithDef (idl, (c, ctx))) ->
    let me_struct, delta = flatten_modtype env mp1 me' me_struct_o in
    let env' = env_for_mtb_with_def env mp1 me_struct delta idl in
    let mt = extract_mexpr_spec env mp1 (None, me') in
    let sg = Evd.from_env env in
    ( match extract_with_type env' sg (EConstr.of_constr c) with
    (* cb may contain some kn *)
    | None -> mt
    | Some (vl, typ) ->
      type_iter_references Visit.add_ref typ;
      MTwith (mt, ML_With_type (idl, vl, typ)) )
  | MEwith (me', WithMod (idl, mp)) ->
    Visit.add_mp_all mp;
    MTwith (extract_mexpr_spec env mp1 (None, me'), ML_With_module (idl, mp))
  | MEapply _ ->
    (* No higher-order module type in OCaml : we use the expanded version *)
    let me_struct, delta = flatten_modtype env mp1 me_alg me_struct_o in
    extract_msignature_spec env mp1 delta me_struct

and extract_mexpression_spec env mp1 (me_struct, me_alg) =
  match me_alg with
  | MEMoreFunctor me_alg' ->
    let mbid, mtb, me_struct' =
      match me_struct with
      | MoreFunctor (mbid, mtb, me') -> (mbid, mtb, me')
      | _ -> assert false
    in
    let mp = MPbound mbid in
    let env' = Modops.add_module_type mp mtb env in
    MTfunsig
      ( mbid,
        extract_mbody_spec env mp mtb,
        extract_mexpression_spec env' mp1 (me_struct', me_alg') )
  | MENoFunctor m -> extract_mexpr_spec env mp1 (Some me_struct, m)

and extract_msignature_spec env mp1 reso = function
  | NoFunctor struc ->
    let env' = Modops.add_structure mp1 struc reso env in
    MTsig (mp1, extract_structure_spec env' mp1 reso struc)
  | MoreFunctor (mbid, mtb, me) ->
    let mp = MPbound mbid in
    let env' = Modops.add_module_type mp mtb env in
    MTfunsig
      ( mbid,
        extract_mbody_spec env mp mtb,
        extract_msignature_spec env' mp1 reso me )

and extract_mbody_spec : 'a. _ -> _ -> 'a generic_module_body -> _ =
 fun env mp mb ->
   match mb.mod_type_alg with
   | Some ty -> extract_mexpression_spec env mp (mb.mod_type, ty)
   | None ->
     (* Fall back to expanding the signature *)
     extract_msignature_spec env mp mb.mod_delta mb.mod_type

(** Recursively extracts a module structure to ML declarations. When all=false,
    only extracts needed declarations based on dependency analysis. Evaluation
    order (last to first) ensures correct dependencies. *)
let rec extract_structure access env mp reso ~all = function
  | [] -> []
  | (l, SFBconst cb) :: struc ->
    ( try
        let sg = Evd.from_env env in
        (* An instance of a singleton class is extracted as an instance,
           whatever its body: the fixpoint is its method's. *)
        if singleton_instance_class ~env (GlobRef.ConstRef (make_cst reso mp l)) <> None then
          raise Impossible;
        let vl, is_fix, recd, struc = factor_fix env sg l cb struc in
        let vc = Array.map (make_cst reso mp) vl in
        let ms = extract_structure access env mp reso ~all struc in
        let b = Array.exists Visit.needed_cst vc in
        if all || b then
          let d = extract_fixpoint env sg vc is_fix recd in
          if (not b) && logical_decl d then
            ms
          else (
            (* Skip dependency tracking for fixpoints whose bodies are
               entirely replaced by inline-custom C++ code. *)
            if not (Array.for_all
                      (fun c -> is_inline_custom (GlobRef.ConstRef c)) vc) then
              Visit.add_decl_deps d;
            (l, SEdecl d) :: ms )
        else
          ms
      with Impossible ->
        let ms = extract_structure access env mp reso ~all struc in
        let c = make_cst reso mp l in
        let b = Visit.needed_cst c in
        if all || b then
          let d = extract_constant access env c cb in
          if (not b) && logical_decl d then
            ms
          else (
            (* Skip dependency tracking for constants whose bodies are
               replaced by inline-custom C++ code. *)
            if not (is_inline_custom (GlobRef.ConstRef c)) then
              Visit.add_decl_deps d;
            (l, SEdecl d) :: ms )
        else
          ms )
  | (l, SFBmind mib) :: struc ->
    let ms = extract_structure access env mp reso ~all struc in
    let mind = make_mind reso mp l in
    let b = Visit.needed_ind mind in
    if all || b then
      let d = Dind (mind, extract_inductive env mind) in
      (* An all-[Prop] inductive has no C++ meaning: nothing that reaches it
         spells it, because every position it could occupy erases.  Drop it
         even when something asked for it -- a [Prop] type reached through a
         type argument marks it needed, and emitting it then puts an enum in
         the header that no declaration refers to. *)
      if logical_decl d then
        ms
      else (
        (* Skip dependency tracking for inductives with a custom
           C++ extraction — their Rocq definitions are not emitted. *)
        if not (is_custom (GlobRef.IndRef (mind, 0))) then
          Visit.add_decl_deps d;
        (l, SEdecl d) :: ms )
    else
      ms
  | (l, SFBrules rrb) :: struc ->
    let b =
      List.exists (fun (cst, _) -> Visit.needed_cst cst) rrb.rewrules_rules
    in
    let ms = extract_structure access env mp reso ~all struc in
    if all || b then (
      List.iter
        (fun (cst, _) -> Table.add_symbol_rule (ConstRef cst) l)
        rrb.rewrules_rules;
      ms )
    else
      ms
  | (l, SFBmodule mb) :: struc ->
    let ms = extract_structure access env mp reso ~all struc in
    let mp = MPdot (mp, l) in
    (* Skip module if it's in the skip module set *)
    if is_skip_module mp then
      ms
    else
      let all' = all || Visit.needed_mp_all mp in
      if all' || Visit.needed_mp mp then
        (l, SEmodule (extract_module access env mp ~all:all' mb)) :: ms
      else
        ms
  | (l, SFBmodtype mtb) :: struc ->
    let ms = extract_structure access env mp reso ~all struc in
    let mp = MPdot (mp, l) in
    (* Skip module type if it's in the skip module set *)
    if is_skip_module mp then
      ms
    else if all || Visit.needed_mp mp then
      (l, SEmodtype (extract_mbody_spec env mp mtb)) :: ms
    else
      ms

(** Extracts a module expression (functor application, module identifier, etc.).
    Handles MEident, MEapply, and expands module expressions as needed. *)
and extract_mexpr access env mp = function
  | MEwith _ -> assert false (* no 'with' syntax for modules *)
  | me when lang () != Cpp ->
    (* In Haskell/Scheme, we expand everything. For now, we also extract
       everything, dead code will be removed later (see
       [Modutil.optimize_struct]. *)
    let sign, delta = expand_mexpr env mp me in
    extract_msignature access env mp delta ~all:true sign
  | MEident mp ->
    if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false;
    Visit.add_mp_all mp;
    Miniml.MEident mp
  | MEapply (me, arg) ->
    Miniml.MEapply
      (extract_mexpr access env mp me, extract_mexpr access env mp (MEident arg))

(** Extracts a module expression with functor support. Handles both MENoFunctor
    (simple module) and MEMoreFunctor (functor) cases. *)
and extract_mexpression access env mp mty = function
  | MENoFunctor me -> extract_mexpr access env mp me
  | MEMoreFunctor me ->
    let mbid, mtb, mty =
      match mty with
      | MoreFunctor (mbid, mtb, mty) -> (mbid, mtb, mty)
      | NoFunctor _ -> assert false
    in
    let mp1 = MPbound mbid in
    let env' = Modops.add_module_type mp1 mtb env in
    Miniml.MEfunctor
      ( mbid,
        extract_mbody_spec env mp1 mtb,
        extract_mexpression access env' mp mty me )

and extract_msignature access env mp reso ~all = function
  | NoFunctor struc ->
    let env' = Modops.add_structure mp struc reso env in
    Miniml.MEstruct (mp, extract_structure access env' mp reso ~all struc)
  | MoreFunctor (mbid, mtb, me) ->
    let mp1 = MPbound mbid in
    let env' = Modops.add_module_type mp1 mtb env in
    Miniml.MEfunctor
      ( mbid,
        extract_mbody_spec env mp1 mtb,
        extract_msignature access env' mp reso ~all me )

(** Builds the ML module structure for a given module body. Extracts both the
    implementation and type signature. *)
and extract_module access env mp ~all mb =
  (* A module has an empty [mod_expr] when : - it is a module variable (for
     instance X inside a Module F [X:SIG]) - it is a module assumption (Declare
     Module). Since we look at modules from outside, we shouldn't have
     variables. But a Declare Module at toplevel seems legal (cf #2525). For the
     moment we don't support this situation. *)
  let impl =
    match Declareops.mod_expr mb with
    | Abstract -> error_no_module_expr mp
    | Algebraic me -> extract_mexpression access env mp mb.mod_type me
    | Struct sign ->
      (* This module has a signature, otherwise it would be FullStruct. We
         extract just the elements required by this signature. *)
      let () = add_labels mp mb.mod_type in
      let sign = Modops.annotate_struct_body sign mb.mod_type in
      extract_msignature access env mp mb.mod_delta ~all:false sign
    | FullStruct ->
      extract_msignature access env mp mb.mod_delta ~all mb.mod_type
  in
  (* Slight optimization: for modules without explicit signatures ([FullStruct]
     case), we build the type out of the extracted implementation *)
  let typ =
    match Declareops.mod_expr mb with
    | FullStruct ->
      assert (Option.is_empty mb.mod_type_alg);
      mtyp_of_mexpr impl
    | Algebraic fae when Option.is_empty mb.mod_type_alg ->
      (* For module applications without explicit type, try to infer from
         functor *)
      let inferred_alg_type =
        match fae with
        | MENoFunctor me ->
          ( match me with
          | MEapply (func, _) ->
            (* Handle both simple (MEident) and nested (MEapply) functor
               applications *)
            let rec get_base_functor = function
              | MEident mp -> Some mp
              | MEapply (f, _) -> get_base_functor f
              | _ -> None
            in
            ( match get_base_functor func with
            | Some func_mp ->
              ( try
                  let func_mb = Global.lookup_module func_mp in
                  (* Extract the return type from the functor signature *)
                  let rec get_functor_return_type = function
                    | MEMoreFunctor fae -> get_functor_return_type fae
                    | MENoFunctor me ->
                      (* For MEwith, extract just the base module type *)
                      let rec extract_base_from_with = function
                        | MEwith (me', _) -> extract_base_from_with me'
                        | base -> base
                      in
                      Some (MENoFunctor (extract_base_from_with me))
                  in
                  match func_mb.mod_type_alg with
                  | Some alg -> get_functor_return_type alg
                  | None -> None
                with _ -> None )
            | None -> None )
          | _ -> None )
        | MEMoreFunctor _ -> None
      in
      ( match inferred_alg_type with
      | Some alg_ty -> extract_mexpression_spec env mp (mb.mod_type, alg_ty)
      | None -> extract_mbody_spec env mp mb )
    | _ -> extract_mbody_spec env mp mb
  in
  {ml_mod_expr = impl; ml_mod_type = typ}

(** Extracts a monomorphic environment for the given references and module
    paths. Computes which declarations are needed and builds ML structures. *)
let mono_environment ~opaque_access refs mpl =
  Visit.reset ();
  List.iter Visit.add_ref refs;
  List.iter Visit.add_mp_all mpl;
  let env = Global.env () in
  let l = List.rev (environment_until None) in
  List.rev_map
    (fun (mp, struc) ->
      ( mp,
        extract_structure
          opaque_access
          env
          mp
          no_delta
          ~all:(Visit.needed_mp_all mp)
          struc ) )
    l

(**************************************)
(** {1 Part II : Input/Output primitives} *)
(**************************************)

(** Returns the language descriptor for the current extraction target. *)
let descr () =
  match lang () with
  | Cpp -> Cpp.cpp_descr

(* From a filename string "foo.cpp" or "foo", builds "foo.cpp" and "foo.h" Works
   similarly for the other languages. *)

let default_id = Id.of_string "Main"

(** BDE-flavored standard headers using [bsl_*] naming. *)
let header_imports_bsl =
  [
    "bsl_concepts.h";
    "bsl_functional.h";
    "bsl_iostream.h";
    "bsl_memory.h";
    "bsl_stdexcept.h";
    "bsl_string.h";
    "bsl_type_traits.h";
    "bsl_variant.h";
    "bsl_vector.h";
  ]

let mk_include s = str ("#include <" ^ s ^ ">")
let mk_include_quoted s = str ("#include \"" ^ s ^ "\"")

(** True when BDE (Bloomberg Development Environment) mode is active. *)
let is_bde () = String.equal (Table.std_lib ()) "BDE"

(** Compute the include guard macro name for a given filename. *)
let include_guard_name s =
  let base = Filename.basename s in
  let name = Filename.remove_extension base in
  String.uppercase_ascii ("INCLUDED_" ^ name)

(** Generates the [#include] block for a C++ implementation file.
    Standard and custom headers are omitted for non-BDE mode because they
    are already included transitively via the component's own header (both
    share the same accumulator). *)
let header fn () =
  (* The producing binary, named by the artifact itself under [CRANE_STAMP]:
     see {!Table.stamp_build}.  The implementation file is stamped as well as
     the header because both are compared, and a witness on one of two files
     leaves the other saying nothing. *)
  let build_stamp =
    if Table.stamp_build () then
      str ("// crane-plugin " ^ Table.plugin_build_stamp ()) ++ fnl ()
    else mt ()
  in
  (* Component's own header must be first include (BDE Rule 5.5) *)
  let self_include =
    build_stamp
    ++
    match fn with
    | Some s ->
      let s = Filename.basename s in
      let hdr = Filename.remove_extension s ^ ".h" in
      mk_include_quoted hdr ++ fnl ()
    | None -> mt ()
  in
  if is_bde () then
    let imps = get_custom_imports () in
    let himports = header_imports_bsl in
    let h =
      List.fold_left
        (fun p s -> p ++ mk_include s ++ fnl ())
        (str "")
        (himports @ imps)
    in
    self_include
    ++ fnl ()
    ++ h
    ++ fnl2 ()
    ++ str "namespace BloombergLP {"
    ++ fnl2 ()
    ++ str "}"
  else
    self_include ++ fnl2 ()

(** Generates the header file preamble: include guard, includes, and BDE
    concept boilerplate (if applicable). *)
let spec_header ?(unit_includes = []) si () =
  (* Headers of the units that already emitted libraries this one depends on
     come first: they are the reason those declarations are absent below. *)
  let imps = List.map (fun u -> u ^ ".h") unit_includes @ get_custom_imports () in
  let himports =
    if is_bde () then
      let needed = Table.required_standard_headers () in
      let extra_std =
        List.filter (fun h -> List.mem h needed)
          ["any"; "atomic"; "deque"; "utility"]
      in
      header_imports_bsl @ extra_std
    else Table.required_standard_headers ()
  in
  (* The producing binary, named by the artifact itself under [CRANE_STAMP]:
     see {!Table.stamp_build}.  Ahead of the include guard so it survives a
     second inclusion being skipped, and a comment so nothing downstream reads
     it. *)
  let build_stamp =
    if Table.stamp_build () then
      str ("// crane-plugin " ^ Table.plugin_build_stamp ()) ++ fnl ()
    else mt ()
  in
  (* Include guard (BDE Rule 4.2.3): #ifndef INCLUDED_NAME *)
  let guard_name = Option.map include_guard_name si in
  let guard_open =
    build_stamp
    ++
    match guard_name with
    | Some g ->
      str ("#ifndef " ^ g) ++ fnl () ++ str ("#define " ^ g) ++ fnl2 ()
    | None -> mt ()
  in
  let h =
    List.fold_left
      (fun p s -> p ++ mk_include s ++ fnl ())
      (str "")
      (himports @ imps)
  in

  (* [Set Crane Arena] master switch.  Defined before the runtime headers
     (arena.h / rc.h) are pulled in below so rc.h's arena-backed control-block
     fields and its [arena.h] include are compiled in.  When the switch is off
     this line is absent and rc.h compiles with no arena machinery at all,
     keeping the runtime minimal for programs that never use an arena. *)
  let h =
    if Table.arena_enabled () then
      h ++ str "#define CRANE_ARENA 1" ++ fnl ()
    else
      h
  in
  (* [crane::fn], the closure representation, counts its references
     non-atomically under the same policy as [crane::rc].  The macro comes
     before any runtime header, since lazy.h and crane_fn.h include fn.h
     themselves. *)
  let h =
    if Table.non_atomic_rc () then
      h ++ str "#define CRANE_NON_ATOMIC_RC 1" ++ fnl ()
    else
      h
  in
  (* [Crane SingleThreaded]: the block heap is one global (pool.h), likewise
     ahead of every runtime header. *)
  let h =
    if Table.single_threaded () then
      h ++ str "#define CRANE_SINGLE_THREADED 1" ++ fnl ()
    else
      h
  in
  let h =
    if Table.demanded Crane_rt.fn_header then
      h ++ mk_include_quoted Crane_rt.fn_header ++ fnl ()
    else
      h
  in
  let h =
    if Table.demanded Crane_rt.variant_header then
      h ++ mk_include_quoted Crane_rt.variant_header ++ fnl ()
    else
      h
  in
  let h =
    if Table.demanded Crane_rt.shared_variant_header then
      h ++ mk_include_quoted Crane_rt.shared_variant_header ++ fnl ()
    else
      h
  in
  (* [crane::immortal], for a function's constants (see {!Cpp_constants}). *)
  let h =
    if Table.demanded Crane_rt.shared_block_header then
      h ++ mk_include_quoted Crane_rt.shared_block_header ++ fnl ()
    else
      h
  in
  let h =
    if Table.demanded Crane_rt.field_header then
      h ++ mk_include_quoted Crane_rt.field_header ++ fnl ()
    else
      h
  in
  let h =
    if Table.demanded Crane_rt.obj_header then
      h ++ mk_include_quoted Crane_rt.obj_header ++ fnl ()
    else
      h
  in
  let h =
    if Table.has_any_coinductive () then
      h ++ mk_include_quoted Crane_rt.lazy_header ++ fnl ()
    else
      h
  in
  (* Reified ITree types require the crane_itree.h runtime header.  Only
     add it when the header isn't already pulled in by a user-specified
     [From "crane_itree.h"] directive. *)
  let h =
    if Table.needs_itree_header ()
       && not
            (List.exists
               (fun s -> String.equal s Crane_rt.itree_header)
               (himports @ imps) )
    then
      h ++ mk_include_quoted Crane_rt.itree_header ++ fnl ()
    else
      h
  in
  (* [crane::erase_fn] (for function values stored into erased [std::any]
     fields) lives in the crane_fn.h runtime header so separate extraction does
     not emit the template into every generated header (which would be an ODR
     redefinition when several are included in one translation unit). *)
  let h =
    if Table.needs_erase_fn ()
       && not
            (List.exists
               (fun s -> String.equal s Crane_rt.erasure_header)
               (himports @ imps) )
    then
      h ++ mk_include_quoted Crane_rt.erasure_header ++ fnl ()
    else
      h
  in
  (* [crane::arena]/[arena_alloc] (for opt-in arena-mode recursive inductives)
     live in the arena.h runtime header. *)
  let h =
    if Table.needs_arena ()
       && not (List.exists (fun s -> String.equal s "arena.h") (himports @ imps))
    then
      h ++ mk_include_quoted "arena.h" ++ fnl ()
    else
      h
  in
  (* [crane::rc]/[crane::make_rc]/[crane::enable_rc_from_this] (the non-atomic
     reference-counted pointer selected by [Crane NonAtomicRc]) live in rc.h. *)
  let h =
    if Table.non_atomic_rc ()
       && not (List.exists (fun s -> String.equal s "rc.h") (himports @ imps))
    then
      h ++ mk_include_quoted "rc.h" ++ fnl ()
    else
      h
  in
  (* [crane::counting_ptr] (the measurement-only reference-count-counting
     shared pointer selected by [CRANE_COUNT_RC]) lives in count_rc.h. *)
  let h =
    if Table.count_rc ()
       && not (List.exists (fun s -> String.equal s "count_rc.h") (himports @ imps))
    then
      h ++ mk_include_quoted "count_rc.h" ++ fnl ()
    else
      h
  in
  (* [crane::small_vector] (the small-buffer-optimized destructor drain
     worklist) lives in small_vector.h. *)
  let h =
    if Table.needs_small_vector ()
       && not (List.exists (fun s -> String.equal s "small_vector.h") (himports @ imps))
    then
      h ++ mk_include_quoted "small_vector.h" ++ fnl ()
    else
      h
  in
  (* The generated destructor drains establish sole ownership with
     [use_count() == 1] before mutating a node in place.  Against an atomic
     control block that relaxed load needs an acquire fence to pair with the
     release-decrement of the owner that dropped the other reference, so those
     drains reach for [std::atomic_thread_fence].  [Crane NonAtomicRc] emits no
     fence and so needs no include. *)
  let h =
    if Table.needs_small_vector () && not (Table.non_atomic_rc ())
       && not (List.exists (fun s -> String.equal s "atomic") (himports @ imps))
    then
      h ++ mk_include "atomic" ++ fnl ()
    else
      h
  in
  (* A unit that spawns threads needs atomic counts in every shared runtime
     block it can reach, and within one translation unit the policy is fixed
     by whichever runtime header came first -- possibly another unit's, under
     [Crane NonAtomicRc].  That is checked here, after every include, so it is
     a compile error rather than a race. *)
  let h =
    if Table.unit_is_concurrent () then
      h
      ++ mk_include_quoted "shared_block.h"
      ++ fnl ()
      ++ str
           "static_assert(crane::rc_is_atomic, \"this unit spawns threads, but \
            a header included before it chose CRANE_NON_ATOMIC_RC\");"
      ++ fnl ()
    else
      h
  in
  let fun_concept =
    if is_bde () then
      "template <class From, class To>\n\
       concept convertible_to = bsl::is_convertible<From, To>::value;\n\n\
       template <class T, class U>\n\
       concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, \
       T>::value;"
    else
      ""
  in
  if is_bde () then
    guard_open
    ++ h
    ++ fnl2 ()
    ++ str "using namespace BloombergLP;"
    ++ fnl ()
    ++ str fun_concept
    ++ fnl2 ()
  else
    guard_open
    ++ h
    ++ fnl2 ()
    ++ str fun_concept
    ++ fnl2 ()

(** Generate include guard closing for header files. *)
let spec_footer si () =
  match si with
  | Some s ->
    let guard = include_guard_name s in
    fnl () ++ str ("#endif // " ^ guard) ++ fnl ()
  | None -> mt ()

(** Computes the (impl_file, header_file, module_id) triple for monolithic
    extraction from an optional filename. *)
let mono_filename f =
  let d = descr () in
  match f with
  | None -> (None, None, default_id)
  | Some f ->
    let f =
      if Filename.check_suffix f d.file_suffix then
        Filename.chop_suffix f d.file_suffix
      else
        f
    in
    let id = default_id in
    let f =
      if Filename.is_relative f then
        Filename.concat (output_directory_for_module ()) f
      else
        f
    in
    (Some (f ^ d.file_suffix), Option.map (( ^ ) f) d.sig_suffix, id)

(** Builds (impl_file, header_file, module_id) for a module file path in
    separate extraction mode. *)
let module_filename mp =
  let f = file_of_modfile mp in
  let id = Id.of_string f in
  let f = Filename.concat (output_directory_for_module ()) f in
  let d = descr () in
  let fimpl_base = d.file_naming mp ^ d.file_suffix in
  let fimpl = Filename.concat (output_directory_for_module ()) fimpl_base in
  (Some fimpl, Option.map (( ^ ) f) d.sig_suffix, id)

(** The steps of {!plan_layout}, in order. *)
let prepare_layout = "prepare"
let plan_names = "plan_names"
let plan_referenced_names = "plan_referenced_names"
let plan_field_names = "plan_field_names"
let plan_pointer_fields = "plan_pointer_fields"
let plan_unmerged_wrappers = "plan_unmerged_wrappers"
let plan_promoted_inductives = "plan_promoted_inductives"
let plan_accessors = "plan_accessors"
let plan_nested_structs = "plan_nested_structs"
let plan_scopes = "plan_scopes"
let plan_instance_promoted_types = "plan_instance_promoted_types"
let plan_callables = "plan_callables"
let install_callables = "install_callables"

let layout_pass_names =
  [ prepare_layout;
    plan_names;
    plan_referenced_names;
    plan_field_names;
    plan_pointer_fields;
    plan_unmerged_wrappers;
    plan_scopes;
    plan_promoted_inductives;
    plan_accessors;
    plan_nested_structs;
    plan_instance_promoted_types;
    plan_callables;
    install_callables ]

(** Settle the unit's layout -- where each declaration lives and what it is
    called ({!Module_plan}) -- then the names of the modules and the globals
    it declares, in declaration order ({!Cpp.plan_module_names},
    {!Cpp.plan_names}), and those it refers to
    ({!Cpp.plan_referenced_names}), and of its constructors' fields
    ({!Cpp.plan_field_names}), which of those fields are stored behind the
    pointer ({!Cpp.plan_pointer_fields}), which wrapper structs hold
    declarations ({!Cpp.plan_unmerged_wrappers}), which constants are
    accessor functions ({!Cpp.plan_accessors}), and how a definition written
    outside its struct's body names the struct ({!Cpp.plan_scopes}), then
    plan the callable of each
    function and method a render will generate, installing each before the
    next is decided.  Returns all of them, with the callables assumed of the
    functions that have no plan.  Under [CRANE_CHECK_IR] the callables are
    planned a second time with every list reversed, and the two must agree:
    a head is a function of its declaration, not of what was planned before
    it.  Runs in the planning phase, which is the one that names modules. *)
let plan_layout struc =
  set_phase Plan;
  Pipeline_trace.event "layout" prepare_layout;
  let modules = Cpp.prepare_structure struc in
  Install_legacy_plan.install_modules modules;
  Pipeline_trace.event "layout" plan_names;
  let module_names = Cpp.plan_module_names struc in
  let names = Cpp.plan_names struc in
  Pipeline_trace.event "layout" plan_referenced_names;
  let referenced_names = Cpp.plan_referenced_names struc in
  Pipeline_trace.event "layout" plan_field_names;
  let field_names = Cpp.plan_field_names struc in
  Pipeline_trace.event "layout" plan_pointer_fields;
  let pointer_fields = Cpp.plan_pointer_fields struc in
  Install_legacy_plan.install_pointer_fields pointer_fields;
  Pipeline_trace.event "layout" plan_unmerged_wrappers;
  let unmerged_wrappers = Cpp.plan_unmerged_wrappers () in
  Install_legacy_plan.install_unmerged_wrappers unmerged_wrappers;
  Pipeline_trace.event "layout" plan_scopes;
  let scopes = Cpp.plan_scopes struc in
  Install_legacy_plan.install_scopes scopes;
  Pipeline_trace.event "layout" plan_promoted_inductives;
  let promoted_inductives = Cpp.plan_promoted_inductives struc in
  Install_legacy_plan.install_promoted_inductives promoted_inductives;
  Pipeline_trace.event "layout" plan_accessors;
  let accessors = Cpp.plan_accessors struc in
  Install_legacy_plan.install_accessors accessors;
  Pipeline_trace.event "layout" plan_nested_structs;
  let nested_structs = Cpp.plan_nested_structs struc in
  Install_legacy_plan.install_nested_structs nested_structs;
  Pipeline_trace.event "layout" plan_instance_promoted_types;
  let instance_promoted_types = Cpp.plan_instance_promoted_types struc in
  Install_legacy_plan.install_instance_promoted_types instance_promoted_types;
  Pipeline_trace.event "layout" plan_callables;
  let ((callables, instance_methods) as planned) = Cpp.plan_callables struc in
  if
    Sys.getenv_opt "CRANE_CHECK_IR" <> None
    &&
    let callables', instance_methods' = Cpp.plan_callables ~reversed:true struc in
    not
      ( Target_plan.same_callables callables callables'
      && Target_plan.same_instance_methods instance_methods instance_methods' )
  then CErrors.anomaly Pp.(str "Crane: planning the callables in reverse order decided differently.");
  let assumed = Translation_calls.assumed_callables struc callables in
  Pipeline_trace.event "layout" install_callables;
  Install_legacy_plan.install_callables callables assumed;
  Install_legacy_plan.install_instance_methods instance_methods;
  ( modules,
    { Target_plan.module_names;
      names;
      referenced_names;
      field_names;
      pointer_fields;
      unmerged_wrappers;
      promoted_inductives;
      accessors;
      nested_structs;
      scopes;
      instance_promoted_types },
    planned,
    assumed )

(** The tables' sizes ({!Table.census}), and how many names emission had
    decided ({!Common.names_decided_while_emitting}), at one point of a
    unit's extraction. *)
type checkpoint = {
  census : (string * int) list;
  names_decided : int;
}

let checkpoint () =
  { census = Table.census (); names_decided = List.length (Common.names_decided_while_emitting ()) }

(** The tables that grew from [before] to [after], with how much. *)
let grown before after =
  List.filter_map
    (fun (name, n) ->
      match List.assoc_opt name before.census with
      | Some m when n > m -> Some (name, n - m)
      | None when n > 0 -> Some (name, n)
      | _ -> None )
    after.census

(** Under [CRANE_TRACE_PIPELINE], report what the tables gained from
    [before] to now, while the files were rendered: the headers their text
    demands. *)
let report_decided_while_rendering before =
  if Pipeline_trace.enabled () then
    let grown = grown before (checkpoint ()) in
    Pipeline_trace.event "emit"
      ( "decided while rendering: "
      ^ if grown = [] then "nothing"
        else String.concat ", " (List.map (fun (name, n) -> Printf.sprintf "%s +%d" name n) grown) )

(** The tables generating output ahead of the files may add to: the headers
    what is generated needs, and the names of the helpers lifted out of a
    body as it is generated, which {!Common.names_decided_while_emitting}
    lists for the check below.  Rendering may add to none: the headers are
    demanded from what was generated ({!Cpp_demands}). *)
let generation_products = ["demands"; "ref_renaming"; "mp_renaming"; "global_ids"]

let rendering_products = []

(** Check that generating output decided nothing the plan should have, and
    that rendering it decided nothing at all.

    Every decision about the shape of the code -- a name, a field, whether a
    wrapper merged -- is taken while planning, and generating output only
    reads them.  A table that has grown since planning ended holds a decision
    that emission made, which an earlier use of the same declaration could
    not have seen.  Generation, from [planned] to [generated], may demand
    headers, and names the helpers it lifts out of the bodies it translates
    as it lifts them; any other name it decided is one the plan missed.
    Every body is generated, and every header it needs demanded, before the
    files are rendered, so from [generated] on nothing may be added.

    The corpus satisfies this today.  Reported under [CRANE_CHECK_IR], like
    {!Table.mark_demand}'s late demands, rather than left to surface as C++
    that does not compile. *)
let check_no_late_decisions ~planned ~generated =
  report_decided_while_rendering generated;
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    let late ~stage what =
      CErrors.user_err
        Pp.(
          str "Crane: " ++ what ++ str " while " ++ str stage
          ++ str ".  Decisions belong to planning; a use rendered before \
                  this one could not have seen it." )
    in
    let check ~stage products before after =
      List.iter
        (fun (name, n) ->
          if not (List.mem name products) then
            late ~stage Pp.(int n ++ str " entries were added to '" ++ str name ++ str "'") )
        (grown before after)
    in
    let rendered = checkpoint () in
    check ~stage:"output was being generated" generation_products planned generated;
    check ~stage:"the files were being rendered" rendering_products generated rendered;
    List.iteri
      (fun i decided ->
        let stage =
          if i < generated.names_decided then "output was being generated"
          else "the files were being rendered"
        in
        match decided with
        | Common.Global_name r when i < generated.names_decided && Option.has_some (Lifted.of_ref r) -> ()
        | Common.Global_name r ->
          late ~stage Pp.(str "the name of " ++ str (Table.kername_of_global r) ++ str " was decided")
        | Common.Module_name mp ->
          late ~stage Pp.(str "the name of module " ++ str (ModPath.to_string mp) ++ str " was decided") )
      (Common.names_decided_while_emitting ())
  end

(** {2 Extraction of a ml struct to a file} *)

(** For Recursive Extraction, writing directly on stdout won't work with
    rocqide, we use a buffer instead *)

let buf = Buffer.create 1000

(** Creates a [Format.formatter] for output. In dry-run mode, discards all
    output. When no file is given, writes to [buf]. *)
let formatter dry file =
  let ft =
    if dry then
      Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    else
      match file with
      | Some f -> Format.formatter_of_out_channel f
      | None -> Format.formatter_of_buffer buf
  in
  (* We never want to see ellipsis ... in extracted code *)
  Format.pp_set_max_boxes ft max_int;
  (* Reuse the width from "Set Printing Width" if the user set one *)
  ( match Topfmt.get_margin () with
  | None -> ()
  | Some i ->
    Format.pp_set_margin ft i;
    Format.pp_set_max_indent ft (i - 10) );
  (* note: max_indent should be < margin above, otherwise it's ignored *)
  ft

(** Returns the user-set file comment, or [None] if empty. *)
let get_comment () =
  let s = file_comment () in
  if String.is_empty s then None else Some s

(** Checks if an executable is available on the system PATH. Returns true if the
    executable can be found. *)
let executable_available exe =
  Subprocess.executable_available exe

let bde_format_available () = executable_available "bde-format"

let clang_format_available () = executable_available "clang-format"

(** How long the formatter may take on [text] before Crane keeps it as
    written.  Crane's output formats at about 2 ms a line, but clang-format's
    line breaking can blow up on a long, fully qualified, template-heavy
    expression -- a 4700-line separately extracted Vellvm header ran for
    minutes and grew past 10 GB -- so a file taking ten times the usual rate
    is abandoned, and none is given more than two minutes: a whole-program
    header the size of Vellvm's would take most of an hour even at the usual
    rate, and is better kept as written. *)
let format_budget text =
  let lines = ref 0 in
  String.iter (fun c -> if c = '\n' then incr lines) text;
  Float.min 120. (30. +. (0.02 *. float_of_int !lines))

(** Whether the formatter was killed for running past {!format_budget}, in
    which case [what] is reported as left unformatted. *)
let format_timed_out what = function
  | Unix.WSIGNALED s when s = Sys.sigkill ->
    Feedback.msg_warning
      Pp.(
        str "the formatter ran out of time on" ++ spc () ++ str what ++ str ";"
        ++ spc () ++ str "leaving it unformatted" );
    true
  | _ -> false

(** Formats a buffer using clang-format or bde-format. Returns the formatted
    string, or the original buffer contents if formatting fails. *)
let format_buffer_to_string (buf : Buffer.t) : string =
  if Table.format_style () = "None" then
    Buffer.contents buf
  else
    let use_bde = Table.format_style () = "BDE" in
    let formatter, formatter_args, available =
      if use_bde then
        ("bde-format", [], bde_format_available ())
      else
        ( "clang-format",
          ["-style=" ^ Table.format_style ()],
          clang_format_available () )
    in
    if not available then (
      Feedback.msg_warning
        Pp.(
          str (if use_bde then "bde-format" else "clang-format")
          ++ spc ()
          ++ str "not found: skipping formatting" );
      Buffer.contents buf )
    else
      let raw_output = Buffer.contents buf in
      match
        Subprocess.filter ~timeout:(format_budget raw_output) formatter
          formatter_args raw_output
      with
      | exception _ -> raw_output
      | {status = Unix.WEXITED 0; stdout; _} -> stdout
      | {status; _} ->
        ignore (format_timed_out "the generated code" status);
        raw_output

(** Runs [clang-format -i] (or [bde-format]) on [filename] in place. No-op
    if the formatter is unavailable or style is set to ["None"]. *)
let format_file_inplace (filename : string) : unit =
  let skip_format = Table.format_style () = "None" in
  let use_bde = Table.format_style () = "BDE" || is_bde () in
  let available =
    if use_bde then
      bde_format_available ()
    else
      clang_format_available ()
  in
  if not available then
    Feedback.msg_warning
      Pp.(
        str (if use_bde then "bde-format" else "clang-format")
        ++ spc ()
        ++ str "not found: skipping formatting" )
  else
    let formatter, formatter_args =
      if use_bde then
        ("bde-format", ["-i"; filename])
      else
        ("clang-format", ["-i"; "-style=" ^ Table.format_style (); filename])
    in
    if skip_format then
      ()
    else
      let timeout =
        format_budget (In_channel.with_open_bin filename In_channel.input_all)
      in
      ignore
        (format_timed_out filename
           (Subprocess.run ~timeout formatter formatter_args) )

(** Filter applied to [opened_libraries ()] in [print_structure_to_file] to
    prune back-edges in the inter-module include graph during separate
    extraction.  A back-edge exists when module X includes module Y but Y is
    topologically earlier than X (Y comes before X in the extraction order and
    therefore Y's content is already (or will be) included when X is compiled).
    The default is no-op; [separate_extraction] sets it per module. *)
let opened_filter : (ModPath.t -> bool) ref = ref (fun _ -> true)

(** Under [CRANE_COUNT_GENERATION], report how many top-level bodies each
    phase generated for the unit written to [fn]. *)
let report_body_generations fn =
  if Sys.getenv_opt "CRANE_COUNT_GENERATION" <> None then
    Feedback.msg_notice
      Pp.(
        str "Crane: bodies generated for "
        ++ str (Option.default "<stdout>" fn)
        ++ str ": "
        ++ prlist_with_sep (fun () -> str ", ")
             (fun (p, n) -> str (phase_name p) ++ str " " ++ int n)
             (Gen_decls.body_generation_counts ()) )

(** [Modutil.optimize_struct], one body for coinciding definitions, a
    recursive function specialized to the lambda a definition passes it, and
    then {!Normalize}, so that every consumer of the structure (the
    method registry built before printing as much as the printer) sees the
    same bodies, and a body a rewrite introduces meets Normalize's contract
    like any other. *)
let core_passes to_appear : ml_structure Pipeline_trace.pass list =
  let open Pipeline_trace in
  [ pass "modutil" (Modutil.optimize_struct to_appear);
    (* Which inductives are shared variants is a property of their
       declarations, final from here; the method registry {!Normalize} builds
       already asks. *)
    effect "shared_variants" Structure_analysis.register_shared_variants;
    pass "dedup" Ml_dedup.structure;
    pass "specialize" Ml_specialize.structure;
    pass "fix_shape" Fix_shape.structure;
    pass "normalize" Normalize.structure;
    effect "local_types" Local_types.structure;
    effect "ir_check" Ml_ir_check.structure ]

let core_pass_names = Pipeline_trace.names (core_passes ([], []))

(** Under [CRANE_TRACE_PIPELINE], report the fingerprint of [struc]; under
    it or [CRANE_CHECK_IR], keep its elements' for
    {!check_structure_unchanged}. *)
let observed_fingerprint ~stage struc =
  if Pipeline_trace.enabled () then
    Pipeline_trace.event stage
      ("fingerprint " ^ Ml_fingerprint.to_hex (Ml_fingerprint.structure struc));
  if Pipeline_trace.enabled () || Probe.checking () then Some (Ml_fingerprint.elements struc)
  else None

(** Report the elements rendering changed, and under [CRANE_CHECK_IR] fail
    if there is one.

    Everything the plan records is a fact about one structure, and emission
    reads those facts back against the structure it is handed, so a structure
    that changes while it is rendered is read by emission as a different
    program from the one that was planned. *)
let check_structure_unchanged planned struc =
  Option.iter
    (fun before ->
      let changed =
        List.filter_map
          (fun ((l, fp), (_, fp')) -> if Ml_fingerprint.equal fp fp' then None else Some l)
          (List.combine before (Ml_fingerprint.elements struc))
      in
      List.iter
        (fun l -> Pipeline_trace.event "emit" ("changed by rendering: " ^ Label.to_string l))
        changed;
      if changed <> [] then
        Probe.violation "frozen program"
          Pp.(
            str "rendering changed "
            ++ prlist_with_sep pr_comma Label.print changed) )
    planned

(** [freeze core]: the frozen program ({!Core.freeze}), with the facts the
    whole of it is analysed for -- which definitions only throw, which
    parameters are owned, settled across calls -- installed before any unit
    is planned ({!Program_facts.analyze_program}). *)
let freeze core =
  let frozen = Core.freeze core in
  Pipeline_trace.event "core" "analyze_program";
  Install_legacy_plan.install_program (Program_facts.analyze_program frozen);
  frozen

let optimize_struct to_appear struc =
  let core =
    Core.optimize (Pipeline_trace.run ~stage:"core" (core_passes to_appear)) (Core.extracted struc)
  in
  if Pipeline_trace.enabled () then ignore (observed_fingerprint ~stage:"core" (Core.structure core));
  core

(** The steps of {!analyze_and_plan}, in order. *)
let analyze_program = "analyze_program"
let plan_target = "plan_target"
let install_plan = "install_legacy_plan"
let plan_pass_names = [analyze_program; plan_target; install_plan]

(** Analyse the unit's structure ({!Program_facts}), decide what the backend
    makes of it ({!Target_plan}), and install both for the readers not yet
    converted.  Both are values computed from the structure alone; under
    [CRANE_CHECK_IR] each is computed twice and the two must agree, which is
    what lets a plan stand for its input. *)
let analyze_and_plan struc =
  Pipeline_trace.event "plan" analyze_program;
  let facts = Program_facts.analyze struc in
  Pipeline_trace.event "plan" plan_target;
  let plan = Target_plan.plan facts struc in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    let facts' = Program_facts.analyze struc in
    if
      not
        (Program_facts.equal facts facts'
        && Target_plan.equal plan (Target_plan.plan facts' struc))
    then CErrors.anomaly Pp.(str "Crane: planning the same structure twice decided differently.")
  end;
  Pipeline_trace.event "plan" install_plan;
  Install_legacy_plan.install struc facts plan;
  (facts, plan)

(** What a unit decides about its structure before its layout, in order.
    [namespace] is the C++ namespace of a separately extracted file. *)
let unit_passes ~namespace : ml_structure Pipeline_trace.pass list =
  let open Pipeline_trace in
  [ (* The used customs decide whether this unit can spawn a thread, which is
       what resolves a [Crane NonAtomicRc] or [Crane SingleThreaded]
       request. *)
    effect "non_atomic_rc" (fun _ -> Table.check_non_atomic_rc_request ());
    (* This file's demands start from nothing, so that one file's needs don't
       leak into a later file of a separate extraction. *)
    effect "reset_demands" (fun _ -> Table.reset_demands ());
    (* In separate extraction, cross-module references are fully qualified
       ([Datatypes::List] rather than [List]). *)
    effect "cross_file_qualification" (fun _ ->
        if namespace <> None then Common.set_force_cross_file_qualification () ) ]

let unit_pass_names = Pipeline_trace.names (unit_passes ~namespace:None)

(** The steps of {!plan_representation}, in order. *)
let template_kinds = "template_kinds"
let install_template_kinds = "install_template_kinds"
let represent_pass_names = [template_kinds; install_template_kinds]

(** The steps run on the unit's Core once its target is planned, in order. *)
let elaborate_calls = "elaborate_calls"
let plan_foreign_callables = "plan_foreign_callables"
let elaborate_pass_names = [elaborate_calls; plan_foreign_callables]

(** Elaborate every call of [struc] and install the elaborations, then plan
    the callables of the globals it names that it does not declare. *)
let elaborate_unit struc =
  Pipeline_trace.event "elaborate" elaborate_calls;
  let elaborations = Core_elaborate.structure struc in
  Core_elaborate.install elaborations;
  Pipeline_trace.event "elaborate" plan_foreign_callables;
  Callable_abi.install_foreign
    (fun r -> Translation_calls.callee_abi ~instances:0 r)
    (Core_elaborate.referenced elaborations)

(** Decide the kinds of the template parameters of the unit's inductives and
    type aliases, into [plan], and install them for the readers not yet
    converted.  They are decided from the inductive kinds {!analyze_and_plan}
    installed, so after it.  Deciding records each as it goes (see
    {!Cpp_ind.template_kinds}); under [CRANE_CHECK_IR] they are decided a
    second time, against the first's, and the two must agree. *)
let plan_representation plan struc =
  Pipeline_trace.event "represent" template_kinds;
  let kinds = Cpp_ind.template_kinds struc in
  let plan = Target_plan.with_template_kinds plan kinds in
  if
    Sys.getenv_opt "CRANE_CHECK_IR" <> None
    && not (Target_plan.equal plan (Target_plan.with_template_kinds plan (Cpp_ind.template_kinds struc)))
  then CErrors.anomaly Pp.(str "Crane: planning the same structure twice decided differently.");
  Pipeline_trace.event "represent" install_template_kinds;
  Install_legacy_plan.install_template_kinds plan;
  plan

(** Whether the unit [struc] declares a reference: an inductive of its, a
    constructor, a record field, a constant, a module type's specification;
    a functor's body included. *)
let declares struc =
  let declared = ref Ref.User.Set.empty in
  let add r = declared := Ref.User.Set.add r !declared in
  let inductive kn ind =
    ( match ind.ind_kind with
    | Record fields | TypeClass fields -> List.iter (fun (f, _) -> Option.iter add f) fields
    | Standard | Coinductive -> () );
    Array.iteri
      (fun i p ->
        add (GlobRef.IndRef (kn, i));
        Array.iteri (fun j _ -> add (GlobRef.ConstructRef ((kn, i), j + 1))) p.ip_types )
      ind.ind_packets
  in
  Modutil.struct_iter
    (function
      | Dind (kn, ind) -> inductive kn ind
      | Dtype (r, _, _) | Dterm (r, _, _) -> add r
      | Dfix fds -> List.iter (fun fd -> add fd.fd_ref) fds )
    (function
      | Sind (kn, ind) -> inductive kn ind
      | Stype (r, _, _) | Sval (r, _, _) -> add r )
    ignore struc;
  fun r -> Ref.User.Set.mem r !declared

(** Renders an entire ML structure to C++ header and implementation files:
    plans the unit, renders each file once, then writes and formats them. *)
let print_structure_to_file ?(namespace = None) ?(unit_includes = [])
    (fn, si, mo) dry core =
  let struc = Core.structure core in
  Buffer.clear buf;
  let d = descr () in
  (* Empties every per-file cell, the mutual-recursion registry among them,
     before this unit is planned and rendered.  Everything before the first
     render is planning, whatever the previous unit left the phase at. *)
  reset_renaming_tables ();
  set_phase Plan;
  let unsafe_needs =
    {
      mldummy = struct_ast_search Mlutil.isMLdummy struc;
      tdummy = struct_type_search Mlutil.isTdummy struc;
      tunknown = struct_type_search (( == ) Tunknown) struc;
      magic = false;
    }
  in
  let facts, plan = analyze_and_plan struc in
  ignore (Pipeline_trace.run ~stage:"unit" (unit_passes ~namespace) struc);
  let plan = plan_representation plan struc in
  let planned = observed_fingerprint ~stage:"unit" struc in
  let modules, representation, callables, assumed = plan_layout struc in
  let plan = Target_plan.with_layout plan modules representation callables assumed in
  elaborate_unit struc;
  let planned_checkpoint = checkpoint () in
  freeze_global_ids ();
  (* Both bodies are rendered before either file is opened.  A preamble has to
     say what the body it precedes demands -- which headers it includes, which
     unsafe features it uses -- and the body is the only thing that knows.
     Rendering first and writing after lets the preamble follow from the body
     that is actually written.  Everything raised after this point is too
     late, which [freeze_demands] is there to catch.

     Neither render may depend on the other having run, so
     [CRANE_RENDER_ORDER=intf-first] renders the header first: an order
     dependence then shows as a difference in the generated files.  Nor may
     a render depend on having run before: [CRANE_RENDER_TWICE] renders both
     files again once both are rendered, and fails unless each comes out the
     same (the plan's Milestone 9). *)
  let render_impl () =
    set_phase (Emit Impl);
    Pipeline_trace.event "emit" "render_impl";
    d.pp_struct struc
  in
  let render_intf () =
    set_phase (Emit Intf);
    Pipeline_trace.event "emit" "render_intf";
    d.pp_hstruct struc
  in
  let intf_first = Sys.getenv_opt "CRANE_RENDER_ORDER" = Some "intf-first" in
  (* Every function is generated before either render, emitting as the file
     rendered first does: calls read the plans emission reads. *)
  let first = if intf_first then Intf else Impl in
  set_phase (Emit first);
  Cpp_state.writing_file first (fun () ->
      Pipeline_trace.event "emit" "generate_ahead";
      Cpp.generate_ahead struc;
      Common.plan_written_files (Cpp.files_named_ahead struc);
      Pipeline_trace.event "emit" "plan_file_layout";
      Cpp.plan_file_layout struc;
      Pipeline_trace.event "emit" "plan_ctor_aliases";
      Cpp.plan_ctor_aliases struc );
  let generated_checkpoint = checkpoint () in
  let body_impl, body_hstruct =
    if intf_first then
      let intf = render_intf () in
      (render_impl (), intf)
    else
      let impl = render_impl () in
      (impl, render_intf ())
  in
  if Sys.getenv_opt "CRANE_RENDER_TWICE" <> None then begin
    (* As documents: a string of one depends on the formatter's state. *)
    let same body again = Stdlib.compare body again = 0 in
    let impl_again = render_impl () in
    let intf_again = render_intf () in
    if not (same body_impl impl_again && same body_hstruct intf_again) then
      CErrors.anomaly
        Pp.(str "Crane: rendering " ++ str (Option.default "<stdout>" fn)
            ++ str " again gave another document.")
  end;
  report_body_generations fn;
  Table.freeze_demands ();
  Common.check_written_files ();
  check_no_late_decisions ~planned:planned_checkpoint ~generated:generated_checkpoint;
  Generated_program.check_against_plan ~declares:(declares struc);
  Generated_program.check_against_ahead ();
  Install_legacy_plan.check_installed facts plan;
  check_structure_unchanged planned struc;
  if Pipeline_trace.enabled () then begin
    Pipeline_trace.event "emit" (Core_elaborate.report ());
    Pipeline_trace.event "emit" (Core_effects.report ());
    Pipeline_trace.event "emit" (Callable_abi.report_foreign ())
  end;
  let opened = List.filter !opened_filter (opened_libraries ()) in
  let ns_open =
    match namespace with
    | Some ns -> str ("namespace " ^ ns ^ " {") ++ fnl2 ()
    | None -> mt ()
  in
  let ns_close =
    match namespace with
    | Some ns -> fnl () ++ str ("} // namespace " ^ ns) ++ fnl ()
    | None -> mt ()
  in
  (* Print the implementation *)
  let cout = if dry then None else Option.map open_out fn in
  let ft = formatter dry cout in
  let comment = get_comment () in
  ( try
      (* The real printing of the implementation *)
      pp_with ft (header fn ());
      pp_with ft (d.preamble mo comment opened unsafe_needs);
      pp_with ft ns_open;
      pp_with ft body_impl;
      pp_with ft ns_close;
      (* If a [main] function returning a monad was found, it was renamed to
         [_main].  Generate a [main()] wrapper.  In reified mode the wrapper
         calls [_main()->run()] to execute the ITree; in sequential mode (monad
         erased) it just calls [_main()] directly. *)
      ( match Table.get_main_function () with
      | Some (main_name, _ret_ml_ty, struct_qual, needs_run) ->
        let qualified_name =
          match struct_qual with
          | Some sn -> Id.print sn ++ str "::" ++ Id.print main_name
          | None -> Id.print main_name
        in
        let call =
          if needs_run then
            qualified_name ++ str "()->run();"
          else
            qualified_name ++ str "();"
        in
        let wrapper =
          str "\n" ++
          str "int main() {" ++ fnl () ++
          str "  " ++ call ++ fnl () ++
          str "  return 0;" ++ fnl () ++
          str "}" ++ fnl ()
        in
        pp_with ft wrapper
      | None -> () );
      Format.pp_print_flush ft ();
      Option.iter close_out cout
    with reraise ->
      Format.pp_print_flush ft ();
      Option.iter close_out cout;
      raise reraise );
  (* If not a dry run, format the output file with clang-format *)
  if not dry then (
    Option.iter format_file_inplace fn;
    Option.iter info_file fn );
  (* Now, let's print the signature *)
  Option.iter
    (fun si ->
      let cout = open_out si in
      let ft = formatter false (Some cout) in
      ( try
          pp_with ft (spec_header ~unit_includes (Some si) ());
          pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
          pp_with ft ns_open;
          pp_with ft body_hstruct;
          pp_with ft ns_close;
          pp_with ft (spec_footer (Some si) ());
          Format.pp_print_flush ft ();
          close_out cout
        with reraise ->
          Format.pp_print_flush ft ();
          close_out cout;
          raise reraise );
      (* Format the signature file with clang-format *)
      format_file_inplace si;
      info_file si )
    (if dry then None else si);
  (* When extracting to the response window (no files), also print the signature
     part so users can see both .h and .cpp outputs. *)
  if (not dry) && fn = None && si = None then (
    let ft = formatter false None in
    try
      pp_with ft (fnl2 () ++ str "/* Signature (.h) */" ++ fnl ());
      pp_with ft (spec_header ~unit_includes None ());
      pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
      pp_with ft ns_open;
      pp_with ft body_hstruct;
      pp_with ft ns_close;
      Format.pp_print_flush ft ()
    with reraise ->
      Format.pp_print_flush ft ();
      raise reraise );
  (* Print the buffer content via Rocq standard formatter (ok with rocqide). *)
  if not (Int.equal (Buffer.length buf) 0) then (
    let formatted_output = format_buffer_to_string buf in
    Feedback.msg_notice (str formatted_output);
    Buffer.reset buf );
  (* Loopify records an outcome per recursive function but reports nothing as
     it goes: a function may be transformed more than once per unit (by the
     implementation and header passes) and only the best of those outcomes
     describes the code actually emitted.  Report now that they are all in,
     and only when the files are written. *)
  if not dry then Loopify.report_outcomes ~unit_name:(match fn with Some f -> Filename.basename f | None -> "") ()

(*********************************************)
(** {2 Part III: the actual extraction commands} *)
(*********************************************)

(** Resets all extraction state: visit lists, tables, and renaming. *)
let reset () =
  Visit.reset ();
  reset_tables ();
  reset_renaming_tables ();
  set_phase Plan;
  Miniml.Meta.thaw ()

(** Initializes the extraction environment, checking section scope and setting
    mode flags (modular/library/compute). *)
let init ?(compute = false) ?(inner = false) modular library =
  if not inner then check_inside_section ();
  set_keywords (descr ()).keywords;
  set_global_scope_keywords (descr ()).global_scope_keywords;
  set_modular modular;
  set_library library;
  set_extrcompute compute;
  Cpp_state.reset_cpp_state ();
  (* Reset ALL C++ global state from previous extractions *)
  reset ()

(** Emits warnings about opaque constants and axioms encountered during
    extraction. *)
let warns () =
  warning_opaques (access_opaque ());
  warning_axioms ()

(* From a list of [reference], let's retrieve whether they correspond to modules
   or [global_reference]. Warn the user if both is possible. *)

(** Separates a list of qualified names into global references and module
    paths, warning when a name is ambiguous between both. *)
let rec locate_ref = function
  | [] -> ([], [])
  | qid :: l ->
    let mpo = try Some (Nametab.locate_module qid) with Not_found -> None
    and ro =
      try Some (Smartlocate.global_with_alias qid)
      with Nametab.GlobalizationError _ | UserError _ -> None
    in
    ( match (mpo, ro) with
    | None, None -> Nametab.error_global_not_found ~info:Exninfo.null qid
    | None, Some r ->
      let refs, mps = locate_ref l in
      (r :: refs, mps)
    | Some mp, None ->
      let refs, mps = locate_ref l in
      (refs, mp :: mps)
    | Some mp, Some r ->
      warning_ambiguous_name ?loc:qid.CAst.loc (qid, mp, r);
      let refs, mps = locate_ref l in
      (refs, mp :: mps) )

(** Derives the output source file path from extraction target. Resolves paths
    like _build/default/../../tests/basics/nat/nat.cpp to
    tests/basics/nat/Nat.v. Returns empty string if source file cannot be
    determined uniquely. *)
let derive_source_file filename =
  try
    let dir = Filename.dirname filename in
    let files = Sys.readdir dir |> Array.to_list in
    let v_files = List.filter (fun f -> Filename.check_suffix f ".v") files in
    match v_files with
    | [v] ->
      let full_path = Filename.concat dir v in
      (* Strip _build/default/ and ../../ prefixes that dune adds *)
      let cleaned =
        if String.starts_with ~prefix:"_build/default/" full_path then
          String.sub full_path 15 (String.length full_path - 15)
        else if String.starts_with ~prefix:"../../" full_path then
          String.sub full_path 6 (String.length full_path - 6)
        else
          full_path
      in
      (* Resolve remaining ../ and ./ references by walking the path
         components *)
      let parts = String.split_on_char '/' cleaned in
      let rec resolve acc = function
        | [] -> List.rev acc
        | ".." :: rest ->
          (* Go up one directory by popping from accumulator *)
          ( match acc with
          | _ :: tail -> resolve tail rest
          | [] -> resolve acc rest )
        | "." :: rest -> resolve acc rest
        | part :: rest -> resolve (part :: acc) rest
      in
      let resolved = String.concat "/" (resolve [] parts) in
      (* If still absolute, make relative to current working directory *)
      if String.length resolved > 0 && resolved.[0] = '/' then
        let cwd = Sys.getcwd () in
        if String.starts_with ~prefix:(cwd ^ "/") resolved then
          String.sub
            resolved
            (String.length cwd + 1)
            (String.length resolved - String.length cwd - 1)
        else
          resolved
      else
        resolved
    | _ -> "" (* Not exactly one .v file - can't determine source uniquely *)
  with _ -> ""

(** {2 Recursive extraction in the Rocq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when
    extracting to a file with the command: \verb!Extraction "file"! [qualid1]
    ... [qualidn]} *)

(** Core of recursive extraction: extracts the given references and module
    paths, optimizes, and writes to a monolithic output file. *)
type export = {ex_ref : GlobRef.t; ex_name : string; ex_unit : string}

(** The C++ expression for Rocq's [tt] under the active mappings and naming. *)
let cpp_unit () =
  match Table.resolve_tt_ctor () with
  | Some tt when Table.is_custom tt -> Table.find_custom tt
  | Some (GlobRef.ConstructRef ((kn, index), constructor_index)) ->
    pp_global Type (GlobRef.IndRef (kn, index))
    ^ "::"
    ^ Common.enum_ctor_name_of_ref kn index constructor_index
  | _ -> CErrors.anomaly Pp.(str "Crane could not resolve Rocq's unit constructor.")

(** What the unit just printed exports, read while its naming tables are live:
    each requested constant, and [tt], as spelled from where the constant is
    declared. *)
let exports refs =
  let export r =
    let base, _ = Table.labels_of_ref r in
    with_visibility (toplevel_visibility [base]) (fun () ->
        {ex_ref = r; ex_name = pp_global Term r; ex_unit = cpp_unit ()} )
  in
  List.filter_map
    (function GlobRef.ConstRef _ as r -> Some (export r) | _ -> None)
    refs

(** A full extraction, returning [read refs], which runs while the naming
    tables the unit was printed with are still live. *)
let full_extr_reading opaque_access f (refs, mps) read =
  init false false;
  Fun.protect
    ~finally:reset
    (fun () ->
      List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
      let core =
        optimize_struct (refs, mps) (mono_environment ~opaque_access refs mps)
      in
      (* A Rocq library that an earlier extraction already emitted belongs to
         that unit.  Re-emitting it here would define the same symbols a second
         time, so linking both units would fail; this unit includes that unit's
         header and drops the library from its own output.  The libraries that
         remain are claimed for this unit, for the next extraction to see. *)
      let foreign, core =
        match f with
        | None -> ([], core)
        | Some target ->
          (* Only a library from another file can be dropped.  Several modules
             of the file being compiled are routinely extracted into units of
             their own, and each of those extractions sees the same enclosing
             [MPfile]; dropping it after the first would silently emit
             nothing. *)
          let current = MPfile (Lib.library_dp ()) in
          let foreign, own =
            Core.partition
              (fun mp ->
                (not (ModPath.equal mp current))
                &&
                match Table.extracted_unit_of mp with
                | Some unit -> not (String.equal unit target)
                | None -> false )
              core
          in
          List.iter (fun (mp, _) -> Table.claim_extracted_unit mp target) (Core.modules own);
          (List.map fst (Core.modules foreign), own)
      in
      let unit_includes =
        List.sort_uniq String.compare (List.filter_map Table.extracted_unit_of foreign)
      in
      warns ();
      let filenames = mono_filename f in
      (* Parse doc comments from the source .v file, if available *)
      ( match filenames with
      | Some fn, _, _ ->
        let source = derive_source_file fn in
        if source <> "" then
          Doc_comments.set_table (Doc_comments.parse_file source)
      | _ -> () );
      print_structure_to_file ~unit_includes filenames false (freeze core);
      read refs )

let full_extr opaque_access f refs =
  full_extr_reading opaque_access f refs (fun _ -> ())

(** Main entry point for full library extraction. Extracts the given references
    and module paths to a single output file.

    [validate] (default [true]) claims the output filename, rejecting one that
    would escape the output directory or that an earlier extraction already
    took; trusted callers that supply an already-vetted or internal path
    (e.g. a temporary file) pass [~validate:false]. *)
let full_extraction ?(validate = true) ~opaque_access f lr =
  if validate then Option.iter Table.claim_output_target f;
  full_extr opaque_access f (locate_ref lr)

let full_extraction_exports ?(validate = true) ~opaque_access f lr =
  if validate then Option.iter Table.claim_output_target f;
  full_extr_reading opaque_access f (locate_ref lr) exports

(** {2 Separate extraction is similar to recursive extraction, with the output
    decomposed in many files, one per Rocq .v file} *)

(** Prints [struc], one structure per Rocq library, one file per library,
    each in a namespace of its own: [Separate Extraction]'s layout, and
    [Extraction Library]'s.  The file of a library [dry] says is rendered but
    not written. *)
let print_per_library ~dry core =
  let struc = Core.structure core in
  (* Run all per-unit cleanup in [~finally] so state is reset even when the
     body aborts. *)
  Fun.protect
    ~finally:(fun () ->
      Cpp_state.clear_global_method_registry ();
      Cpp_state.clear_valid_output_modules ();
      Cpp_state.clear_global_unmerged ();
      Common.clear_non_output_modules () )
  @@ fun () ->
  (* Descend through applications/functors to the underlying struct body,
     returning its substructure (or [] for a bare module identifier). *)
  let rec module_substructs = function
    | MEstruct (_, s) -> s
    | MEapply (me, _) -> module_substructs me
    | MEfunctor (_, _, me) -> module_substructs me
    | MEident _ -> []
  in
  warns ();
  (* Skip modules whose declarations are all custom-extracted (they would
     produce empty files containing only boilerplate headers). *)
  let decl_refs = Modutil.declared_refs in
  let has_real_decls sel =
    List.exists
      (fun (_, se) ->
        match se with
        | SEdecl d ->
          List.exists (fun r -> not (is_any_custom r)) (decl_refs d)
        | SEmodule _ | SEmodtype _ -> true )
      sel
  in
  (* Check whether a namespace name collides with any top-level declaration
     inside the module (e.g. concept OrderedType inside namespace OrderedType). *)
  let ref_label = function
    | GlobRef.ConstRef c -> Label.to_string (Constant.label c)
    | GlobRef.IndRef (ind, _) -> Label.to_string (MutInd.label ind)
    | GlobRef.ConstructRef ((ind, _), _) -> Label.to_string (MutInd.label ind)
    | GlobRef.VarRef v -> Id.to_string v
  in
  let decl_names = function
    | Dtype (r, _, _) -> [ref_label r]
    | (Dterm _ | Dfix _) as d ->
      List.map (fun fd -> ref_label fd.fd_ref) (Mlutil.term_defs d)
    | Dind (kn, ind) ->
      Array.to_list (Array.map (fun ip -> Id.to_string ip.ip_typename) ind.ind_packets)
  in
  let ns_collides_with_decl ns sel =
    List.exists
      (fun (_, se) ->
        match se with
        | SEdecl d -> List.exists (String.equal ns) (decl_names d)
        | _ -> false )
      sel
  in
  let valid_mps =
    List.filter_map (fun (mp, sel) -> if has_real_decls sel then Some mp else None) struc
  in
  Cpp_state.set_valid_output_modules valid_mps;
  Common.set_non_output_modules valid_mps;
  (* Build a topological position map for all extracted modules.  The struc
     list is already in topological order (each module after its dependencies).
     We use positions to prune forward includes (A includes B where B comes
     after A in topo order) which would create circular C++ #include cycles. *)
  let topo_index : (ModPath.t, int) Hashtbl.t = Hashtbl.create 64 in
  List.iteri (fun i (mp, _) -> Hashtbl.replace topo_index mp i) struc;
  let rec pre_scan_unmerged sel =
    let refs_unmerged_functor (me : ml_module_expr) =
      let rec get_base : ml_module_expr -> bool = function
        | MEapply (me2, _) -> get_base me2
        | MEident mp ->
          let lbl = match mp with
            | ModPath.MPdot (_, l) -> Some (String.capitalize_ascii (Label.to_string l))
            | _ -> None
          in
          (match lbl with Some n -> Cpp_state.is_global_unmerged n | None -> false)
        | MEfunctor (_, _, me2) -> get_base me2
        | MEstruct _ -> false
      in get_base me
    in
    List.iter (fun (l, se) ->
      match se with
      | SEmodule { ml_mod_expr = MEident _; _ } -> ()
      | SEmodule m ->
        let subs = module_substructs m.ml_mod_expr in
        let has_funcs = List.exists (fun (_, se') ->
          match se' with
          | SEdecl (Dterm _ | Dfix _) -> true
          | _ -> false
        ) subs in
        let is_unmerged_apply = refs_unmerged_functor m.ml_mod_expr in
        if has_funcs || is_unmerged_apply then begin
          let name = String.capitalize_ascii (Label.to_string l) in
          Cpp_state.mark_global_unmerged name
        end;
        pre_scan_unmerged subs
      | _ -> ()
    ) sel
  in
  List.iter (fun (_, sel) -> pre_scan_unmerged sel) struc;
  let modtype_table : (ModPath.t, ml_module_type) Hashtbl.t = Hashtbl.create 16 in
  let rec collect_modtypes mp_prefix sel =
    List.iter (fun (l, se) ->
      match se with
      | SEmodtype mt ->
        let mt_mp = Names.ModPath.MPdot (mp_prefix, l) in
        Hashtbl.replace modtype_table mt_mp mt
      | SEmodule m ->
        let sub_mp = Names.ModPath.MPdot (mp_prefix, l) in
        (match m.ml_mod_expr with
         | MEstruct (_, subs) -> collect_modtypes sub_mp subs
         | _ -> ())
      | _ -> ()
    ) sel
  in
  List.iter (fun (mp, sel) -> collect_modtypes mp sel) struc;
  let rec pre_scan_meyers_singletons ~in_template sel =
    List.iter (fun (_l, se) ->
      match se with
      | SEdecl ((Dterm _ | Dfix _) as d) ->
        List.iter
          (fun {fd_ref = r; fd_type = ty; _} ->
            let is_function = match ty with Tarr _ -> true | _ -> false in
            if in_template && not is_function then
              Cpp_state.register_template_static_accessor_ref r
            else if not in_template && not is_function then
              Hashtbl.replace Cpp_state.non_accessor_labels (Table.label_of_r r) () )
          (Mlutil.term_defs d)
      | SEmodule m ->
        let has_params = match m.ml_mod_expr with
          | MEfunctor _ -> true
          | _ -> false
        in
        let sub_in_template = in_template || has_params in
        let rec register_modtype_accessors modtype_table ?param_mp = function
          | MTsig (_, sig_items) ->
            List.iter (fun (l, specif) ->
              match specif with
              | Spec (Sval (r, _, ty)) ->
                let is_function = match ty with Tarr _ -> true | _ -> false in
                if not is_function then begin
                  let lbl = Table.label_of_r r in
                  Cpp_state.register_template_static_accessor
                    (Table.modpath_of_r r) lbl;
                  Option.iter
                    (fun pmp ->
                      Cpp_state.register_template_static_accessor pmp lbl )
                    param_mp
                end
              | Smodule mt ->
                let sub_param_mp = match param_mp with
                  | Some pmp -> Some (Names.ModPath.MPdot (pmp, l))
                  | None -> None
                in
                register_modtype_accessors modtype_table ?param_mp:sub_param_mp mt
              | _ -> ()
            ) sig_items
          | MTfunsig (_, _, mt') -> register_modtype_accessors modtype_table ?param_mp mt'
          | MTwith (mt', _) -> register_modtype_accessors modtype_table ?param_mp mt'
          | MTident mp ->
            (match Hashtbl.find_opt modtype_table mp with
             | Some resolved_mt -> register_modtype_accessors modtype_table ?param_mp resolved_mt
             | None -> ())
        in
        let rec scan_functor_type_params modtype_table = function
          | MTfunsig (mbid, param_mt, body_mt) ->
            let param_mp = Names.ModPath.MPbound mbid in
            register_modtype_accessors modtype_table ~param_mp param_mt;
            scan_functor_type_params modtype_table body_mt
          | _ -> ()
        in
        scan_functor_type_params modtype_table m.ml_mod_type;
        let subs = module_substructs m.ml_mod_expr in
        pre_scan_meyers_singletons ~in_template:sub_in_template subs
      | _ -> ()
    ) sel
  in
  List.iter (fun (_, sel) -> pre_scan_meyers_singletons ~in_template:false sel) struc;
  let file_namespace mp sel =
    let base = ns_of_modfile mp in
    if ns_collides_with_decl base sel then base ^ "_" else base
  in
  List.iter
    (fun (mp, sel) ->
      if is_modfile mp && has_real_decls sel then
        let ns = file_namespace mp sel in
        if not (String.equal ns (ns_of_modfile mp)) then
          Common.rename_file_namespace mp ns )
    struc;
  let print (mp, unit) =
    match (mp, Core.structure unit) with
    | MPfile _, [(_, sel)] ->
      if has_real_decls sel then begin
        let ns = file_namespace mp sel in
        (* Only include modules that are topologically earlier (i.e., come
           before the current module in the extracted structure).  Including a
           later module would create a circular C++ #include cycle. *)
        let current_idx =
          match Hashtbl.find_opt topo_index mp with
          | Some i -> i
          | None -> max_int
        in
        opened_filter :=
          (fun mp' ->
            match Hashtbl.find_opt topo_index mp' with
            | Some j -> j < current_idx
            | None -> true);
        print_structure_to_file ~namespace:(Some ns) (module_filename mp) (dry mp) unit;
        opened_filter := (fun _ -> true)
      end
    | _ -> assert false
  in
  (* Pre-build the method registry from the full structure so that
     cross-module method calls are recognized during per-module rendering. *)
  Cpp_state.set_global_method_registry (Method_registry.create ~ret_is_erased:Translation.return_type_is_erased struc);
  (* Generic traversal of ml_structure: walks MEstruct/MEfunctor/MEapply
     and calls [visit ~in_struct elem] on each structure element. *)
  let iter_structure visit struc =
    let rec walk_elem ~in_struct = function
      | SEmodule m -> walk_mexpr m.ml_mod_expr
      | se -> visit ~in_struct se
    and walk_mexpr = function
      | MEstruct (_, sel) ->
        List.iter (fun (_, se) -> walk_elem ~in_struct:true se) sel
      | MEfunctor (_, _, me) -> walk_mexpr me
      | MEapply (me, _) -> walk_mexpr me
      | MEident _ -> ()
    in
    List.iter (fun (_, sel) ->
      List.iter (fun (_, se) -> walk_elem ~in_struct:false se) sel
    ) struc
  in
  (* Pre-register enum and flat inductives, and struct-member value accessors.
     This global pass runs before any per-module output is generated, so that
     both the struct definition (Defs.h) and any cross-module match code
     (LLPrediction.h) agree on whether an inductive is flat or not. *)
  iter_structure (fun ~in_struct se ->
    match se with
    | SEdecl (Dind (kn, ind)) ->
      let is_mutual = Array.length ind.ind_packets > 1 in
      Array.iteri (fun i _p ->
        let ind_ref = GlobRef.IndRef (kn, i) in
        if not (Table.is_custom ind_ref) && not is_mutual then begin
          if Table.is_enum_inductive_packet ind i then
            Table.add_enum_inductive ind_ref;
          if Table.is_flat_inductive_packet kn ind i then
            Table.add_flat_inductive ind_ref
        end
      ) ind.ind_packets
    | SEdecl ((Dterm _ | Dfix _) as d) when in_struct ->
      List.iter
        (fun {fd_ref = r; fd_type = ty; _} ->
          if (match ty with Tarr _ -> false | _ -> true) then
            Cpp_state.register_template_static_accessor
              (Table.modpath_of_r r) (Table.label_of_r r) )
        (Mlutil.term_defs d)
    | _ -> ()
  ) struc;
  List.iter print (Core.modules core)

(** Entry point for extracting specific references to separate files. Each Rocq
    .v file gets its own C++ output file. *)
let separate_extraction ~opaque_access lr =
  init true false;
  Fun.protect ~finally:reset @@ fun () ->
  let refs, mps = locate_ref lr in
  let core =
    optimize_struct (refs, mps) (mono_environment ~opaque_access refs mps)
  in
  List.iter
    (function
      | MPfile _, _ -> ()
      | (MPdot _ | MPbound _), _ ->
        user_err
          (str "Separate Extraction from inside a module is not supported.") )
    (Core.modules core);
  print_per_library ~dry:(fun _ -> false) (freeze core)

(** {2 Simple extraction in the Rocq toplevel. The vernacular command is
    \verb!Extraction! [qualid]} *)

(** Extracts a single reference or module to the Rocq toplevel output. *)
let simple_extraction ~opaque_access r =
  match locate_ref [r] with
  | ([], [mp]) as p -> full_extr opaque_access None p
  | [r], [] ->
    init false false;
    Fun.protect ~finally:reset (fun () ->
        let core =
          optimize_struct ([r], []) (mono_environment ~opaque_access [r] [])
        in
        warns ();
        if is_any_custom r then
          Feedback.msg_notice (str "/* User defined extraction */" ++ fnl ());
        print_structure_to_file (mono_filename None) false (freeze core) )
  | _ -> assert false

(** {2 (Recursive) Extraction of a library. The vernacular command is
    \verb!(Recursive) Extraction Library! [M]} *)

(** Extracts an entire Rocq library module to separate C++ files. When
    [is_rec] is true, recursively extracts all dependencies. *)
let extraction_library ~opaque_access is_rec CAst.{loc; v = m} =
  init true true;
  Fun.protect ~finally:reset @@ fun () ->
  let dir_m =
    let q = qualid_of_ident m in
    try Nametab.full_name_module q
    with Not_found -> error_unknown_module ?loc q
  in
  Visit.add_mp_all (MPfile dir_m);
  let env = Global.env () in
  let l = List.rev (environment_until (Some dir_m)) in
  let select l (mp, struc) =
    if Visit.needed_mp mp then
      (mp, extract_structure opaque_access env mp no_delta ~all:true struc) :: l
    else
      l
  in
  let struc = List.fold_left select [] l in
  let core = optimize_struct ([], []) struc in
  (* Without [Recursive], only [m]'s own file is written; the libraries it
     depends on are rendered for what [m]'s file needs to know of them. *)
  let dry = function
    | MPfile dir -> (not is_rec) && not (DirPath.equal dir dir_m)
    | _ -> false
  in
  print_per_library ~dry (freeze core)

(* Helper to detect if we're running under dune (for test output formatting).
   When INSIDE_DUNE=1 is set in the environment, we emit machine-parseable
   structured output (CRANE_TEST:STATUS:name:file) instead of pretty messages
   with emojis. This allows run_tests.sh to parse test results reliably. *)
let is_running_in_dune () =
  try
    ignore (Sys.getenv "INSIDE_DUNE");
    true
  with Not_found -> false

(* Helper to emit structured test output for dune. Format:
   CRANE_TEST:STATUS:test_name:source_file where STATUS is one of: PASS,
   FAIL_TEST, FAIL_COMPILE, FAIL_EXTRACT This single-line format avoids the
   multi-line parsing issues we had before. *)
let emit_test_status status test_id_str source_file =
  Feedback.msg_notice
    Pp.(
      str "CRANE_TEST:"
      ++ str status
      ++ str ":"
      ++ str test_id_str
      ++ str ":"
      ++ str source_file )

(** {2 Test-suite: extraction to a temporary file + compilation} *)

(** Full extract-compile-test pipeline: extracts to C++, compiles with clang,
    optionally links and runs the [.t.cpp] test driver, and reports results. *)
let extract_and_compile ~opaque_access file l =
  (* Take the output target, rejecting one that would escape the output
     directory, before it is turned into a path. *)
  Option.iter Table.claim_output_target file;
  let filename =
    match mono_filename file with
    | Some fn, _, _ ->
      let dir =
        Filename.concat
          (Filename.dirname fn)
          (Filename.remove_extension (Filename.basename fn))
      in
      Filename.concat dir (Filename.basename fn)
    | None, _, _ -> Filename.temp_file "testextraction" ".cpp"
  in
  (* Build test identifier like "nat/Nat" for display *)
  let output_name = Filename.remove_extension (Filename.basename filename) in
  let test_id =
    Pp.(str output_name ++ str "/" ++ pr_enum Libnames.pr_qualid l)
  in
  let test_id_str = Pp.string_of_ppcmds test_id in
  (* Check if we're running in dune test mode - determines output format *)
  let in_dune = is_running_in_dune () in
  (* For dune, derive the source .v file path for structured output. For
     interactive use (Proof General, VSCode), we don't need this. *)
  let source_file = if in_dune then derive_source_file filename else "" in
  (* Phase 1: Extract Rocq definitions to C++ code *)
  let extraction_ok =
    try
      (* [filename] is derived internally from the already-validated [file]. *)
      full_extraction ~validate:false ~opaque_access (Some filename) l;
      true
    with exn ->
      (* Emit structured output for dune, or pretty error for interactive use *)
      if in_dune then
        emit_test_status "FAIL_EXTRACT" test_id_str source_file
      else
        (* Report but do not raise: [CErrors.user_err] would abort the whole
           command, skipping cleanup and the final status report below, and
           making the [false] here dead. *)
        Feedback.msg_warning
          Pp.(
            test_id
            ++ spc ()
            ++ str "failed to extract:"
            ++ fnl ()
            ++ str (Printexc.to_string exn)
            ++ fnl ()
            ++ str (Printexc.get_backtrace ()) );
      false
  in
  if extraction_ok then (
    format_file_inplace filename;
    (* Phase 2: Compile the generated C++ code with clang *)
    let compilation_ok =
      try
        Toolchain.compile_cpp ~includes:[Filename.dirname filename] filename;
        true
      with
      | Toolchain.NoClangFound ->
        if in_dune then
          emit_test_status "FAIL_COMPILE" test_id_str source_file
        else
          Feedback.msg_warning
            Pp.(
              test_id ++ spc () ++ str "extracted but clang cannot be found." );
        false
      | Toolchain.ClangError (_exit_code, clang_errors) ->
        if in_dune then
          emit_test_status "FAIL_COMPILE" test_id_str source_file
        else
          Feedback.msg_warning
            ( if !Flags.quiet then
                Pp.(
                  test_id
                  ++ spc ()
                  ++ str "extracted but clang failed to compile." )
              else
                Pp.(
                  test_id
                  ++ spc ()
                  ++ str "extracted but clang failed to compile with:"
                  ++ fnl ()
                  ++ str clang_errors ) );
        false
      | exn ->
        if in_dune then
          emit_test_status "FAIL_COMPILE" test_id_str source_file
        else
          Feedback.msg_warning
            ( if !Flags.quiet then
                Pp.(
                  test_id ++ spc () ++ str "extracted but failed to compile." )
              else
                Pp.(
                  test_id
                  ++ spc ()
                  ++ str "extracted but failed to compile:"
                  ++ fnl ()
                  ++ str (Printexc.to_string exn) ) );
        false
    in
    (* Phase 3: Run test assertions (if any) embedded in the .v file *)
    let tests_ok, out =
      try
        let o = Toolchain.compile_and_test filename in
        (true, o)
      with _ -> (false, "")
    in
    let base = Filename.chop_suffix filename ".cpp" in
    (* Clean up temporary files if this was a temp extraction *)
    if not (Option.has_some file) then (
      if Sys.file_exists filename then Sys.remove filename;
      if Sys.file_exists base then Sys.remove base;
      (* The generated header sits next to the .cpp; remove it too so temp
         extractions don't leave a .h behind. *)
      let header = base ^ ".h" in
      if Sys.file_exists header then Sys.remove header );
    (* Report final status: structured for dune, pretty for interactive *)
    if compilation_ok && tests_ok then
      Feedback.msg_notice
        ( if in_dune then
            Pp.(
              str "CRANE_TEST:PASS:"
              ++ str test_id_str
              ++ str ":"
              ++ str source_file )
          else
            Pp.(
              str "✅ "
              ++ test_id
              ++ spc ()
              ++ str "successfully extracted, compiled, and all tests passed."
              ++ ( if !Flags.quiet || Option.is_empty file then
                     mt ()
                   else
                     spc () ++ str "(" ++ str filename ++ str ")" )
              ++ fnl ()
              ++ str out
              ++ fnl () ) );
    if compilation_ok && not tests_ok then
      Feedback.msg_notice
        ( if in_dune then
            Pp.(
              str "CRANE_TEST:FAIL_TEST:"
              ++ str test_id_str
              ++ str ":"
              ++ str source_file )
          else
            Pp.(
              str "❌ "
              ++ test_id
              ++ spc ()
              ++ str "extracted and compiled, but test assertions failed."
              ++ ( if !Flags.quiet || Option.is_empty file then
                     mt ()
                   else
                     spc () ++ str "(" ++ str filename ++ str ")" )
              ++ fnl () ) ) )

(** {2 Extraction of one decl to stdout} *)

(** Renders the single ML declaration [decl], of the module [mp], to C++
    output, once the unit [struc] it belongs to is planned. *)
let print_one_decl struc mp decl =
  let d = descr () in
  reset_renaming_tables ();
  ignore (plan_layout struc);
  elaborate_unit struc;
  freeze_global_ids ();
  set_phase (Emit Impl);
  let ans =
    Cpp_state.writing_file Impl @@ fun () ->
    with_visibility (toplevel_visibility [mp]) @@ fun () ->
    Cpp.generate_decl_ahead decl;
    d.pp_decl decl
  in
  (* The one box the printers rely on: inside it every break is a newline,
     which is what turns {!Cpp_print.cut2} into the blank line between two
     declaration groups.  Everything else is clang-format's to lay out. *)
  v 0 ans

(* Show the extraction of the current ongoing proof *)
let show_extraction ~pstate =
  init ~inner:true false false;
  let prf = Declare.Proof.get pstate in
  let sigma, env = Declare.Proof.get_current_context pstate in
  let trms = Proof.partial_proof prf in
  let extr_term t =
    let ast, ty = extract_constr env sigma t in
    let mp = Lib.current_mp () in
    let l = Label.of_id (Declare.Proof.get_name pstate) in
    let fake_ref = GlobRef.ConstRef (Constant.make2 mp l) in
    let decl = Dterm (fake_ref, ast, ty) in
    print_one_decl [(mp, [(l, SEdecl decl)])] mp decl
  in
  Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl extr_term trms)
