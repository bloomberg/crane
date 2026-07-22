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
      if (not b) && logical_decl d then
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

(** Standard C++ headers to include in generated implementation files. *)
let header_imports =
  [
    "algorithm";
    "any";
    "cassert";
    "concepts";
    "functional";
    "iostream";
    "memory";
    "optional";
    "stdexcept";
    "string";
    "type_traits";
    "utility";
    "variant";
    "vector";   (* needed by loopify's explicit stack: std::vector<_Frame> *)
  ]

(** Return only the standard headers that were actually referenced during
    rendering.  Falls back to the full list for BDE mode (different naming). *)
let needed_std_headers () =
  let needed = Common.get_needed_headers () in
  List.filter (fun h -> List.mem h needed) header_imports

(** BDE-flavored standard headers using [bsl_*] naming. *)
let header_imports_bsl =
  [
    "bdlf_overloaded.h";
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
    share the same accumulator during the Pre phase). *)
let header fn () =
  (* Component's own header must be first include (BDE Rule 5.5) *)
  let self_include =
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

(** Generates the header file preamble: include guard, includes, BDE concept
    boilerplate (if applicable), and string literals directive. *)
let spec_header si () =
  let imps = get_custom_imports () in
  let himports =
    if is_bde () then
      let needed = Common.get_needed_headers () in
      let extra_std =
        List.filter (fun h -> List.mem h needed)
          ["any"; "deque"; "utility"]
      in
      header_imports_bsl @ extra_std
    else needed_std_headers ()
  in
  (* Include guard (BDE Rule 4.2.3): #ifndef INCLUDED_NAME *)
  let guard_name = Option.map include_guard_name si in
  let guard_open =
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
  let h =
    if Table.has_any_coinductive () then
      h ++ mk_include_quoted "lazy.h" ++ fnl ()
    else
      h
  in
  (* Reified ITree types require the crane_itree.h runtime header.  Only
     add it when the header isn't already pulled in by a user-specified
     [From "crane_itree.h"] directive. *)
  let h =
    if Table.needs_itree_header ()
       && not (List.exists (fun s -> String.equal s "crane_itree.h") (himports @ imps))
    then
      h ++ mk_include_quoted "crane_itree.h" ++ fnl ()
    else
      h
  in
  (* [crane::erase_fn] (for function values stored into erased [std::any]
     fields) lives in the crane_fn.h runtime header so separate extraction does
     not emit the template into every generated header (which would be an ODR
     redefinition when several are included in one translation unit). *)
  let h =
    if Table.needs_erase_fn ()
       && not (List.exists (fun s -> String.equal s "crane_fn.h") (himports @ imps))
    then
      h ++ mk_include_quoted "crane_fn.h" ++ fnl ()
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
  let string_lit_directive =
    if Table.needs_string_literals () then
      if is_bde () then
        fnl () ++ str "using namespace bsl::string_literals;" ++ fnl ()
      else
        fnl () ++ str "using namespace std::string_literals;" ++ fnl ()
    else
      mt ()
  in
  if is_bde () then
    guard_open
    ++ h
    ++ fnl2 ()
    ++ str "using namespace BloombergLP;"
    ++ string_lit_directive
    ++ fnl ()
    ++ str fun_concept
    ++ fnl2 ()
  else
    guard_open
    ++ h
    ++ fnl2 ()
    ++ string_lit_directive
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

(** {2 Extraction of one decl to stdout} *)

(** Renders a single ML declaration to C++ output. Performs renaming and runs
    both Pre and Impl phases. *)
let print_one_decl struc mp decl =
  let d = descr () in
  reset_renaming_tables AllButExternal;
  set_phase Pre;
  ignore (d.pp_struct struc);
  set_phase Impl;
  push_visible mp [];
  let ans = d.pp_decl decl in
  pop_visible ();
  v 0 ans

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

(** Returns the user-set file comment split into words, or [None] if empty. *)
let get_comment () =
  let s = file_comment () in
  if String.is_empty s then
    None
  else
    let split_comment = Str.split (Str.regexp "[ \t\n]+") s in
    Some (prlist_with_sep spc str split_comment)

(** Checks if an executable is available on the system PATH. Returns true if the
    executable can be found. *)
let executable_available exe =
  Subprocess.executable_available exe

let bde_format_available () = executable_available "bde-format"

let clang_format_available () = executable_available "clang-format"

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
      match Subprocess.filter formatter formatter_args raw_output with
      | exception _ -> Buffer.contents buf
      | {status = Unix.WEXITED 0; stdout; _} -> stdout
      | _ -> Buffer.contents buf

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
      ignore (Subprocess.run formatter formatter_args)

(** Scans the ML structure and marks all custom-extracted GlobRefs as "used"
    so their associated [From "header.h"] imports are included. Must run before
    [header()] which reads the used-import set. *)
let mark_used_customs struc =
  Table.reset_used_custom_imports ();
  let mark r = if Table.is_custom r then Table.mark_custom_used r in
  Modutil.struct_iter
    (Modutil.decl_iter_references mark mark mark)
    (Modutil.spec_iter_references mark mark mark)
    (fun _ -> ())
    struc

(** Scans the ML structure for projections used in higher-order positions
    (passed as function values rather than used as field accessors). *)
let mark_higher_order_projections struc =
  Table.init_higher_order_projections ();
  let rec scan_ast = function
    | MLglob (r, _) when Table.is_projection r ->
      Table.mark_higher_order_projection r
    | a -> Mlutil.ast_iter scan_ast a
  in
  let scan_decl = function
    | Dterm (_, a, _) -> scan_ast a
    | Dfix (_, bodies, _) -> Array.iter scan_ast bodies
    | _ -> ()
  in
  Modutil.struct_iter scan_decl (fun _ -> ()) (fun _ -> ()) struc

(** Filter applied to [opened_libraries ()] in [print_structure_to_file] to
    prune back-edges in the inter-module include graph during separate
    extraction.  A back-edge exists when module X includes module Y but Y is
    topologically earlier than X (Y comes before X in the extraction order and
    therefore Y's content is already (or will be) included when X is compiled).
    The default is no-op; [separate_extraction] sets it per module. *)
let opened_filter : (ModPath.t -> bool) ref = ref (fun _ -> true)

(** Renders an entire ML structure to C++ header and implementation files.
    Performs dry run first for renaming, then generates and formats the output.
*)
let print_structure_to_file ?(namespace = None) (fn, si, mo) dry struc =
  Buffer.clear buf;
  let d = descr () in
  reset_renaming_tables AllButExternal;
  let unsafe_needs =
    {
      mldummy = struct_ast_search Mlutil.isMLdummy struc;
      tdummy = struct_type_search Mlutil.isTdummy struc;
      tunknown = struct_type_search (( == ) Tunknown) struc;
      magic = false;
    }
  in
  (* Scan the structure to find which custom constants are actually used, so
     that only their associated imports appear in the generated header. *)
  mark_used_customs struc;
  mark_higher_order_projections struc;
  (* Detect whether any custom inline function is applied to a string literal.
     This determines whether we need 'using namespace std::string_literals;'. *)
  let has_custom_string_arg =
    Modutil.struct_ast_search
      (function
        | MLapp (MLglob (r, _), args) ->
          Table.is_custom r
          && Table.to_inline r
          && List.exists
               (function
                 | MLstring _ -> true
                 | _ -> false )
               args
        | _ -> false )
      struc
  in
  if has_custom_string_arg then
    Table.mark_needs_string_literals ()
  else
    Table.reset_needs_string_literals ();
  (* [crane_erase_fn] is emitted on demand; translation sets the flag when it
     wraps a non-lambda function value stored into an erased field. *)
  Table.reset_needs_erase_fn ();
  (* First, a dry run, for computing objects to rename or duplicate.
     Also accumulates needed standard headers via require_header. *)
  Common.reset_needed_headers ();
  set_phase Pre;
  ignore (d.pp_struct struc);
  ignore (d.pp_hstruct struc);
  let opened = List.filter !opened_filter (opened_libraries ()) in
  (* In separate extraction, force fully qualified cross-module references
     (e.g. Datatypes::List instead of bare List). *)
  ( match namespace with
  | Some _ ->
    Common.mpfiles_clear ();
    Common.set_force_qualified_capitalization ()
  | None -> () );
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
      set_phase Impl;
      pp_with ft (header fn ());
      pp_with ft (d.preamble mo comment opened unsafe_needs);
      pp_with ft ns_open;
      pp_with ft (d.pp_struct struc);
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
          set_phase Intf;
          pp_with ft (spec_header (Some si) ());
          pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
          pp_with ft ns_open;
          pp_with ft (d.pp_hstruct struc);
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
      set_phase Intf;
      pp_with ft (spec_header None ());
      pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
      pp_with ft ns_open;
      pp_with ft (d.pp_hstruct struc);
      pp_with ft ns_close;
      Format.pp_print_flush ft ()
    with reraise ->
      Format.pp_print_flush ft ();
      raise reraise );
  (* Print the buffer content via Rocq standard formatter (ok with rocqide). *)
  if not (Int.equal (Buffer.length buf) 0) then (
    let formatted_output = format_buffer_to_string buf in
    Feedback.msg_notice (str formatted_output);
    Buffer.reset buf )

(*********************************************)
(** {2 Part III: the actual extraction commands} *)
(*********************************************)

(** Resets all extraction state: visit lists, tables, and renaming. *)
let reset () =
  Visit.reset ();
  reset_tables ();
  reset_renaming_tables Everything

(** Initializes the extraction environment, checking section scope and setting
    mode flags (modular/library/compute). *)
let init ?(compute = false) ?(inner = false) modular library =
  if not inner then check_inside_section ();
  set_keywords (descr ()).keywords;
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
let full_extr_with_result opaque_access f (refs, mps) after_print =
  init false false;
  Fun.protect
    ~finally:reset
    (fun () ->
      List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
      let struc =
        optimize_struct (refs, mps) (mono_environment ~opaque_access refs mps)
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
      print_structure_to_file filenames false struc;
      after_print () )

let full_extr opaque_access f refs =
  full_extr_with_result opaque_access f refs (fun () -> ())

(** Main entry point for full library extraction. Extracts the given references
    and module paths to a single output file.

    [validate] (default [true]) rejects an output filename that would escape the
    output directory; trusted callers that supply an already-vetted or internal
    path (e.g. a temporary file) pass [~validate:false]. *)
let full_extraction ?(validate = true) ~opaque_access f lr =
  if validate then Option.iter Table.validate_output_target f;
  full_extr opaque_access f (locate_ref lr)

(** Full extraction variant used by managed benchmarks.  [after_print] runs
    while the exact C++ renaming tables used to print the artifact are still
    available. See {!full_extraction} for [validate]. *)
let full_extraction_with_result ?(validate = true) ~opaque_access f lr after_print
    =
  if validate then Option.iter Table.validate_output_target f;
  full_extr_with_result opaque_access f (locate_ref lr) after_print

(** {2 Separate extraction is similar to recursive extraction, with the output
    decomposed in many files, one per Rocq .v file} *)

(** Entry point for extracting specific references to separate files. Each Rocq
    .v file gets its own C++ output file. *)
let separate_extraction ~opaque_access lr =
  init true false;
  let refs, mps = locate_ref lr in
  let struc =
    optimize_struct (refs, mps) (mono_environment ~opaque_access refs mps)
  in
  let () =
    List.iter
      (function
        | MPfile _, _ -> ()
        | (MPdot _ | MPbound _), _ ->
          user_err
            (str "Separate Extraction from inside a module is not supported.") )
      struc
  in
  warns ();
  (* Skip modules whose declarations are all custom-extracted (they would
     produce empty files containing only boilerplate headers). *)
  let decl_refs = function
    | Dind (kn, _) -> [GlobRef.IndRef (kn, 0)]
    | Dtype (r, _, _) | Dterm (r, _, _) -> [r]
    | Dfix (rv, _, _) -> Array.to_list rv
  in
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
    | Dterm (r, _, _) | Dtype (r, _, _) -> [ref_label r]
    | Dfix (rv, _, _) -> Array.to_list (Array.map ref_label rv)
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
        let subs = match m.ml_mod_expr with
          | MEstruct (_, s) -> s
          | MEapply (me, _) ->
            let rec get_subs = function
              | MEstruct (_, s) -> s
              | MEapply (me2, _) -> get_subs me2
              | MEfunctor (_, _, me2) -> get_subs me2
              | MEident _ -> []
            in get_subs me
          | MEident _ -> []
          | MEfunctor (_, _, me) ->
            let rec get_subs = function
              | MEstruct (_, s) -> s
              | MEapply (me2, _) ->
                let rec get2 = function
                  | MEstruct (_, s) -> s | MEapply (m2, _) -> get2 m2
                  | MEfunctor (_, _, m2) -> get2 m2 | MEident _ -> []
                in get2 me2
              | MEfunctor (_, _, me2) -> get_subs me2
              | MEident _ -> []
            in get_subs me
        in
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
      | SEdecl (Dterm (r, _body, ty)) ->
        let is_function = match ty with Tarr _ -> true | _ -> false in
        if in_template && not is_function then begin
          let mp = Table.modpath_of_r r in
          let lbl = Table.label_of_r r in
          Cpp_state.template_static_accessors :=
            (mp, lbl) :: !Cpp_state.template_static_accessors;
          (match r with
           | GlobRef.ConstRef c ->
             Hashtbl.replace Cpp_state.template_static_accessor_kns
               (Constant.canonical c) ()
           | _ -> ())
        end else if not in_template && not is_function then begin
          let lbl = Table.label_of_r r in
          Hashtbl.replace Cpp_state.non_accessor_labels lbl ()
        end
      | SEdecl (Dfix (refs, _bodies, tys)) ->
        Array.iteri (fun i r ->
          let is_function = match tys.(i) with Tarr _ -> true | _ -> false in
          if in_template && not is_function then begin
            let mp = Table.modpath_of_r r in
            let lbl = Table.label_of_r r in
            Cpp_state.template_static_accessors :=
              (mp, lbl) :: !Cpp_state.template_static_accessors;
            (match r with
             | GlobRef.ConstRef c ->
               Hashtbl.replace Cpp_state.template_static_accessor_kns
                 (Constant.canonical c) ()
             | _ -> ())
          end else if not in_template && not is_function then begin
            let lbl = Table.label_of_r r in
            Hashtbl.replace Cpp_state.non_accessor_labels lbl ()
          end
        ) refs
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
                  let mp = Table.modpath_of_r r in
                  let lbl = Table.label_of_r r in
                  Cpp_state.template_static_accessors :=
                    (mp, lbl) :: !Cpp_state.template_static_accessors;
                  (match param_mp with
                   | Some pmp ->
                     Cpp_state.template_static_accessors :=
                       (pmp, lbl) :: !Cpp_state.template_static_accessors
                   | None -> ())
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
        let subs = match m.ml_mod_expr with
          | MEstruct (_, s) -> s
          | MEfunctor (_, _, me) ->
            let rec get_subs = function
              | MEstruct (_, s) -> s
              | MEfunctor (_, _, me2) -> get_subs me2
              | MEapply (me2, _) -> get_subs me2
              | MEident _ -> []
            in get_subs me
          | MEapply (me, _) ->
            let rec get_subs = function
              | MEstruct (_, s) -> s
              | MEapply (me2, _) -> get_subs me2
              | MEfunctor (_, _, me2) -> get_subs me2
              | MEident _ -> []
            in get_subs me
          | MEident _ -> []
        in
        pre_scan_meyers_singletons ~in_template:sub_in_template subs
      | _ -> ()
    ) sel
  in
  List.iter (fun (_, sel) -> pre_scan_meyers_singletons ~in_template:false sel) struc;
  let print = function
    | ((MPfile _dir as mp), sel) as e ->
      if has_real_decls sel then begin
        let ns =
          let base = ns_of_modfile mp in
          if ns_collides_with_decl base sel then base ^ "_"
          else base
        in
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
        print_structure_to_file ~namespace:(Some ns) (module_filename mp) false [e];
        opened_filter := (fun _ -> true)
      end
    | (MPdot _ | MPbound _), _ -> assert false
  in
  (* Pre-build the method registry from the full structure so that
     cross-module method calls are recognized during per-module rendering.
     The registry creation calls pp_global_name which has side effects on
     mpfiles (include tracking), so save/restore the mpfiles state. *)
  let saved_mpfiles = Common.mpfiles_save () in
  set_phase Pre;
  Cpp_state.set_global_method_registry (Method_registry.create struc);
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
    | SEdecl (Dterm (r, _, ty)) when in_struct ->
      if (match ty with Tarr _ -> false | _ -> true) then
        Cpp_state.register_template_static_accessor
          (Table.modpath_of_r r) (Table.label_of_r r)
    | SEdecl (Dfix (refs, _, tys)) when in_struct ->
      Array.iteri (fun i r ->
        if (match tys.(i) with Tarr _ -> false | _ -> true) then
          Cpp_state.register_template_static_accessor
            (Table.modpath_of_r r) (Table.label_of_r r)
      ) refs
    | _ -> ()
  ) struc;
  set_phase Impl;
  Common.mpfiles_restore saved_mpfiles;
  List.iter print struc;
  Cpp_state.clear_global_method_registry ();
  Cpp_state.clear_valid_output_modules ();
  Cpp_state.clear_global_unmerged ();
  Common.clear_non_output_modules ();
  reset ()

(** {2 Simple extraction in the Rocq toplevel. The vernacular command is
    \verb!Extraction! [qualid]} *)

(** Extracts a single reference or module to the Rocq toplevel output. *)
let simple_extraction ~opaque_access r =
  match locate_ref [r] with
  | ([], [mp]) as p -> full_extr opaque_access None p
  | [r], [] ->
    init false false;
    let struc =
      optimize_struct ([r], []) (mono_environment ~opaque_access [r] [])
    in
    warns ();
    if is_any_custom r then
      Feedback.msg_notice (str "/* User defined extraction */" ++ fnl ());
    print_structure_to_file (mono_filename None) false struc;
    reset ()
  | _ -> assert false

(** {2 (Recursive) Extraction of a library. The vernacular command is
    \verb!(Recursive) Extraction Library! [M]} *)

(** Extracts an entire Rocq library module to separate C++ files. When
    [is_rec] is true, recursively extracts all dependencies. *)
let extraction_library ~opaque_access is_rec CAst.{loc; v = m} =
  init true true;
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
  let struc = optimize_struct ([], []) struc in
  warns ();
  let print = function
    | ((MPfile dir as mp), sel) as e ->
      let dry = (not is_rec) && not (DirPath.equal dir dir_m) in
      print_structure_to_file (module_filename mp) dry [e]
    | _ -> assert false
  in
  List.iter print struc;
  reset ()

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
  (* Reject an output target that would escape the output directory before it is
     turned into a path. *)
  Option.iter Table.validate_output_target file;
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
        ignore
          (CErrors.user_err
             Pp.(
               test_id
               ++ spc ()
               ++ str "failed to extract:"
               ++ fnl ()
               ++ str (Printexc.to_string exn)
               ++ fnl ()
               ++ str (Printexc.get_backtrace ()) ) );
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
          ignore
            (CErrors.user_err
               Pp.(
                 test_id ++ spc () ++ str "extracted but clang cannot be found." ) );
        false
      | Toolchain.ClangError (_exit_code, clang_errors) ->
        if in_dune then
          emit_test_status "FAIL_COMPILE" test_id_str source_file
        else
          ignore
            (CErrors.user_err
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
                     ++ str clang_errors ) ) );
        false
      | exn ->
        if in_dune then
          emit_test_status "FAIL_COMPILE" test_id_str source_file
        else
          ignore
            (CErrors.user_err
               ( if !Flags.quiet then
                   Pp.(
                     test_id ++ spc () ++ str "extracted but failed to compile." )
                 else
                   Pp.(
                     test_id
                     ++ spc ()
                     ++ str "extracted but failed to compile:"
                     ++ fnl ()
                     ++ str (Printexc.to_string exn) ) ) );
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
      if Sys.file_exists base then Sys.remove base );
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
    print_one_decl [] mp decl
  in
  Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl extr_term trms)
