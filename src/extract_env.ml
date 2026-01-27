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
(*S Part I: computing Rocq environment. *)
(****************************************)

let toplevel_env () =
  let mp, struc = Safe_typing.flatten_env (Global.safe_env ()) in
  mp, List.rev struc

let environment_until dir_opt =
  let rec parse = function
    | [] when Option.is_empty dir_opt -> [toplevel_env ()]
    | [] -> []
    | d :: l ->
      let meb =
        Modops.destr_nofunctor (MPfile d) (Global.lookup_module (MPfile d)).mod_type
      in
      match dir_opt with
      | Some d' when DirPath.equal d d' -> [MPfile d, meb]
      | _ -> (MPfile d, meb) :: (parse l)
  in parse (Library.loaded_libraries ())


(*s Visit:
  a structure recording the needed dependencies for the current extraction *)

module type VISIT = sig
  (* Reset the dependencies by emptying the visit lists *)
  val reset : unit -> unit

  (* Add the module_path and all its prefixes to the mp visit list.
     We'll keep all fields of these modules. *)
  val add_mp_all : ModPath.t -> unit

  (* Add reference / ... in the visit lists.
     These functions silently add the mp of their arg in the mp list *)
  val add_ref : GlobRef.t -> unit
  val add_kn : KerName.t -> unit
  val add_decl_deps : ml_decl -> unit
  val add_spec_deps : ml_spec -> unit

  (* Test functions:
     is a particular object a needed dependency for the current extraction ? *)
  val needed_ind : MutInd.t -> bool
  val needed_cst : Constant.t -> bool
  val needed_mp : ModPath.t -> bool
  val needed_mp_all : ModPath.t -> bool
end

module Visit : VISIT = struct
  type must_visit =
      { mutable kn : KNset.t;
        mutable mp : MPset.t;
        mutable mp_all : MPset.t }
  (* the imperative internal visit lists *)
  let v = { kn = KNset.empty; mp = MPset.empty; mp_all = MPset.empty }
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
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp
  let add_mp_all mp =
    check_loaded_modfile mp;
    v.mp <- MPset.union (prefixes_mp mp) v.mp;
    v.mp_all <- MPset.add mp v.mp_all
  let add_kn kn = v.kn <- KNset.add kn v.kn; add_mp (KerName.modpath kn)
  let add_ref = let open GlobRef in function
    | ConstRef c -> add_kn (Constant.user c)
    | IndRef (ind,_) | ConstructRef ((ind,_),_) -> add_kn (MutInd.user ind)
    | VarRef _ -> assert false
  let add_decl_deps = decl_iter_references add_ref add_ref add_ref
  let add_spec_deps = spec_iter_references add_ref add_ref add_ref
end

let add_field_label mp = function
  | (lab, (SFBconst _|SFBmind _ | SFBrules _)) -> Visit.add_kn (KerName.make mp lab)
  | (lab, (SFBmodule _|SFBmodtype _)) -> Visit.add_mp_all (MPdot (mp,lab))

let rec add_labels mp = function
  | MoreFunctor (_,_,m) -> add_labels mp m
  | NoFunctor sign -> List.iter (add_field_label mp) sign

exception Impossible

let check_arity env cb =
  let t = cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let get_body lbody =
  EConstr.of_constr lbody

let check_fix env sg cb i =
  match cb.const_body with
    | Def lbody ->
        (match EConstr.kind sg (get_body lbody) with
          | Fix ((_,j),recd) when Int.equal i j -> check_arity env cb; (true,recd)
          | CoFix (j,recd) when Int.equal i j -> check_arity env cb; (false,recd)
          | _ -> raise Impossible)
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> raise Impossible

let prec_declaration_equal sg (na1, ca1, ta1) (na2, ca2, ta2) =
  Array.equal (Context.eq_annot Name.equal (EConstr.ERelevance.equal sg)) na1 na2 &&
  Array.equal (EConstr.eq_constr sg) ca1 ca2 &&
  Array.equal (EConstr.eq_constr sg) ta1 ta2

let factor_fix env sg l cb msb =
  let _,recd as check = check_fix env sg cb 0 in
  let n = Array.length (let fi,_,_ = recd in fi) in
  if Int.equal n 1 then [|l|], recd, msb
  else begin
    if List.length msb < n-1 then raise Impossible;
    let msb', msb'' = List.chop (n-1) msb in
    let labels = Array.make n l in
    List.iteri
      (fun j ->
         function
           | (l,SFBconst cb') ->
              let check' = check_fix env sg cb' (j+1) in
              if not ((fst check : bool) == (fst check') &&
                        prec_declaration_equal sg (snd check) (snd check'))
               then raise Impossible;
               labels.(j+1) <- l;
           | _ -> raise Impossible) msb';
    labels, recd, msb''
  end

(** Expanding a [module_alg_expr] into a version without abbreviations
    or functor applications. This is done via a detour to entries
    (hack proposed by Elie)
*)

let vm_state =
  (* VM bytecode is not needed here *)
  let vm_handler _ _ _ () = (), None in
  ((), { Mod_typing.vm_handler })

let expand_mexpr env mp me =
  let inl = Some (Flags.get_inline_level()) in
  let state = ((Environ.universes env, Univ.Constraints.empty), Reductionops.inferred_universes) in
  let mb, (_, cst), _ = Mod_typing.translate_module state vm_state env mp inl (MExpr ([], me, None)) in
  mb.mod_type, mb.mod_delta

let expand_modtype env mp me =
  let inl = Some (Flags.get_inline_level()) in
  let state = ((Environ.universes env, Univ.Constraints.empty), Reductionops.inferred_universes) in
  let mtb, _cst, _ = Mod_typing.translate_modtype state vm_state env mp inl ([],me) in
  mtb

let no_delta = Mod_subst.empty_delta_resolver

let flatten_modtype env mp me_alg struc_opt =
  match struc_opt with
  | Some me -> me, no_delta
  | None ->
    let mtb = expand_modtype env mp me_alg in
    mtb.mod_type, mtb.mod_delta

(** Ad-hoc update of environment, inspired by [Mod_typing.check_with_aux_def].
*)

let env_for_mtb_with_def env mp me reso idl =
  let struc = Modops.destr_nofunctor mp me in
  let l = Label.of_id (List.hd idl) in
  let spot = function (l',SFBconst _) -> Label.equal l l' | _ -> false in
  let before = fst (List.split_when spot struc) in
  Modops.add_structure mp before reso env

let make_cst resolver mp l =
  Mod_subst.constant_of_delta_kn resolver (KerName.make mp l)

let make_mind resolver mp l =
  Mod_subst.mind_of_delta_kn resolver (KerName.make mp l)

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to specifications. *)

let rec extract_structure_spec env mp reso = function
  | [] -> []
  | (l,SFBconst cb) :: msig ->
      let c = make_cst reso mp l in
      let s = extract_constant_spec env c cb in
      let specs = extract_structure_spec env mp reso msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmind _) :: msig ->
      let mind = make_mind reso mp l in
      let s = Sind (mind, extract_inductive env mind) in
      let specs = extract_structure_spec env mp reso msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l, SFBrules _) :: msig ->
      let specs = extract_structure_spec env mp reso msig in
      specs
  | (l,SFBmodule mb) :: msig ->
      let specs = extract_structure_spec env mp reso msig in
      let spec = extract_mbody_spec env mb.mod_mp mb in
      (l,Smodule spec) :: specs
  | (l,SFBmodtype mtb) :: msig ->
      let specs = extract_structure_spec env mp reso msig in
      let spec = extract_mbody_spec env mtb.mod_mp mtb in
      (l,Smodtype spec) :: specs

(* From [module_expression] to specifications *)

(* Invariant: the [me_alg] given to [extract_mexpr_spec] and
   [extract_mexpression_spec] should come from a [mod_type_alg] field.
   This way, any encountered [MEident] should be a true module type. *)

and extract_mexpr_spec env mp1 (me_struct_o,me_alg) = match me_alg with
  | MEident mp -> Visit.add_mp_all mp; MTident mp
  | MEwith(me',WithDef(idl,(c,ctx)))->
      let me_struct,delta = flatten_modtype env mp1 me' me_struct_o in
      let env' = env_for_mtb_with_def env mp1 me_struct delta idl in
      let mt = extract_mexpr_spec env mp1 (None,me') in
      let sg = Evd.from_env env in
      (match extract_with_type env' sg (EConstr.of_constr c) with
       (* cb may contain some kn *)
         | None -> mt
         | Some (vl,typ) ->
            type_iter_references Visit.add_ref typ;
            MTwith(mt,ML_With_type(idl,vl,typ)))
  | MEwith(me',WithMod(idl,mp))->
      Visit.add_mp_all mp;
      MTwith(extract_mexpr_spec env mp1 (None,me'), ML_With_module(idl,mp))
  | MEapply _ ->
     (* No higher-order module type in OCaml : we use the expanded version *)
     let me_struct,delta = flatten_modtype env mp1 me_alg me_struct_o in
     extract_msignature_spec env mp1 delta me_struct

and extract_mexpression_spec env mp1 (me_struct,me_alg) = match me_alg with
  | MEMoreFunctor me_alg' ->
      let mbid, mtb, me_struct' = match me_struct with
      | MoreFunctor (mbid, mtb, me') -> (mbid, mtb, me')
      | _ -> assert false
      in
      let mp = MPbound mbid in
      let env' = Modops.add_module_type mp mtb env in
      MTfunsig (mbid, extract_mbody_spec env mp mtb,
                extract_mexpression_spec env' mp1 (me_struct',me_alg'))
  | MENoFunctor m -> extract_mexpr_spec env mp1 (Some me_struct,m)

and extract_msignature_spec env mp1 reso = function
  | NoFunctor struc ->
      let env' = Modops.add_structure mp1 struc reso env in
      MTsig (mp1, extract_structure_spec env' mp1 reso struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp = MPbound mbid in
      let env' = Modops.add_module_type mp mtb env in
      MTfunsig (mbid, extract_mbody_spec env mp mtb,
                extract_msignature_spec env' mp1 reso me)

and extract_mbody_spec : 'a. _ -> _ -> 'a generic_module_body -> _ =
  fun env mp mb -> match mb.mod_type_alg with
  | Some ty -> extract_mexpression_spec env mp (mb.mod_type,ty)
  | None ->
      (* Fall back to expanding the signature *)
      extract_msignature_spec env mp mb.mod_delta mb.mod_type

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to implementations.

   NB: when [all=false], the evaluation order of the list is
   important: last to first ensures correct dependencies.
*)

let rec extract_structure access env mp reso ~all = function
  | [] -> []
  | (l,SFBconst cb) :: struc ->
      (try
         let sg = Evd.from_env env in
         let vl,recd,struc = factor_fix env sg l cb struc in
         let vc = Array.map (make_cst reso mp) vl in
         let ms = extract_structure access env mp reso ~all struc in
         let b = Array.exists Visit.needed_cst vc in
         if all || b then
           let d = extract_fixpoint env sg vc recd in
           if (not b) && (logical_decl d) then ms
           else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
         else ms
       with Impossible ->
         let ms = extract_structure access env mp reso ~all struc in
         let c = make_cst reso mp l in
         let b = Visit.needed_cst c in
         if all || b then
           let d = extract_constant access env c cb in
           if (not b) && (logical_decl d) then ms
           else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
         else ms)
  | (l,SFBmind mib) :: struc ->
      let ms = extract_structure access env mp reso ~all struc in
      let mind = make_mind reso mp l in
      let b = Visit.needed_ind mind in
      if all || b then
        let d = Dind (mind, extract_inductive env mind) in
        if (not b) && (logical_decl d) then ms
        else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
      else ms
  | (l, SFBrules rrb) :: struc ->
      let b = List.exists (fun (cst, _) -> Visit.needed_cst cst) rrb.rewrules_rules in
      let ms = extract_structure access env mp reso ~all struc in
      if all || b then begin
        List.iter (fun (cst, _) -> Table.add_symbol_rule (ConstRef cst) l) rrb.rewrules_rules;
        ms
      end else ms
  | (l,SFBmodule mb) :: struc ->
      let ms = extract_structure access env mp reso ~all struc in
      let mp = MPdot (mp,l) in
      (* Skip module if it's in the skip module set *)
      if is_skip_module mp then ms
      else
        let all' = all || Visit.needed_mp_all mp in
        if all' || Visit.needed_mp mp then
          (l,SEmodule (extract_module access env mp ~all:all' mb)) :: ms
        else ms
  | (l,SFBmodtype mtb) :: struc ->
      let ms = extract_structure access env mp reso ~all struc in
      let mp = MPdot (mp,l) in
      (* Skip module type if it's in the skip module set *)
      if is_skip_module mp then ms
      else if all || Visit.needed_mp mp then
        (l,SEmodtype (extract_mbody_spec env mp mtb)) :: ms
      else ms

(* From [module_expr] and [module_expression] to implementations *)

and extract_mexpr access env mp = function
  | MEwith _ -> assert false (* no 'with' syntax for modules *)
  | me when lang () != Cpp ->
      (* In Haskell/Scheme, we expand everything.
         For now, we also extract everything, dead code will be removed later
         (see [Modutil.optimize_struct]. *)
      let sign, delta = expand_mexpr env mp me in
      extract_msignature access env mp delta ~all:true sign
  | MEident mp ->
      if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false;
      Visit.add_mp_all mp; Miniml.MEident mp
  | MEapply (me, arg) ->
      Miniml.MEapply (extract_mexpr access env mp me,
                      extract_mexpr access env mp (MEident arg))

and extract_mexpression access env mp mty = function
  | MENoFunctor me -> extract_mexpr access env mp me
  | MEMoreFunctor me ->
      let (mbid, mtb, mty) = match mty with
      | MoreFunctor (mbid, mtb, mty) -> (mbid, mtb, mty)
      | NoFunctor _ -> assert false
      in
      let mp1 = MPbound mbid in
      let env' = Modops.add_module_type mp1 mtb	env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec env mp1 mtb,
         extract_mexpression access env' mp mty me)

and extract_msignature access env mp reso ~all = function
  | NoFunctor struc ->
      let env' = Modops.add_structure mp struc reso env in
      Miniml.MEstruct (mp,extract_structure access env' mp reso ~all struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp1 = MPbound mbid in
      let env' = Modops.add_module_type mp1 mtb	env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec env mp1 mtb,
         extract_msignature access env' mp reso ~all me)

and extract_module access env mp ~all mb =
  (* A module has an empty [mod_expr] when :
     - it is a module variable (for instance X inside a Module F [X:SIG])
     - it is a module assumption (Declare Module).
     Since we look at modules from outside, we shouldn't have variables.
     But a Declare Module at toplevel seems legal (cf #2525). For the
     moment we don't support this situation. *)
  let impl = match Declareops.mod_expr mb with
    | Abstract -> error_no_module_expr mp
    | Algebraic me -> extract_mexpression access env mp mb.mod_type me
    | Struct sign ->
      (* This module has a signature, otherwise it would be FullStruct.
         We extract just the elements required by this signature. *)
      let () = add_labels mp mb.mod_type in
      let sign = Modops.annotate_struct_body sign mb.mod_type in
      extract_msignature access env mp mb.mod_delta ~all:false sign
    | FullStruct -> extract_msignature access env mp mb.mod_delta ~all mb.mod_type
  in
  (* Slight optimization: for modules without explicit signatures
     ([FullStruct] case), we build the type out of the extracted
     implementation *)
  let typ = match Declareops.mod_expr mb with
    | FullStruct ->
      assert (Option.is_empty mb.mod_type_alg);
      mtyp_of_mexpr impl
    | Algebraic fae when Option.is_empty mb.mod_type_alg ->
      (* For module applications without explicit type, try to infer from functor *)
      let inferred_alg_type =
        match fae with
        | MENoFunctor me ->
            (match me with
            | MEapply (func, _) ->
                (* Handle both simple (MEident) and nested (MEapply) functor applications *)
                let rec get_base_functor = function
                  | MEident mp -> Some mp
                  | MEapply (f, _) -> get_base_functor f
                  | _ -> None
                in
                (match get_base_functor func with
                | Some func_mp ->
                    (try
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
                      (match func_mb.mod_type_alg with
                      | Some alg -> get_functor_return_type alg
                      | None -> None)
                    with _ -> None)
                | None -> None)
            | _ -> None)
        | MEMoreFunctor _ -> None
      in
      (match inferred_alg_type with
      | Some alg_ty ->
          extract_mexpression_spec env mp (mb.mod_type, alg_ty)
      | None ->
          extract_mbody_spec env mp mb)
    | _ -> extract_mbody_spec env mp mb
  in
  { ml_mod_expr = impl;
    ml_mod_type = typ }

let mono_environment ~opaque_access refs mpl =
  Visit.reset ();
  List.iter Visit.add_ref refs;
  List.iter Visit.add_mp_all mpl;
  let env = Global.env () in
  let l = List.rev (environment_until None) in
  List.rev_map
    (fun (mp,struc) ->
      mp, extract_structure opaque_access env mp no_delta ~all:(Visit.needed_mp_all mp) struc)
    l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with
  | Cpp -> Cpp.cpp_descr
  (* | Rust -> Rust.rust_descr *)

(* From a filename string "foo.cpp" or "foo", builds "foo.cpp" and "foo.h"
   Works similarly for the other languages. *)

let default_id = Id.of_string "Main"

let header_imports = ["functional";"iostream";"memory";"string";"variant"]

let header_imports_bsl = ["bdlf_overloaded.h";"bsl_concepts.h";"bsl_functional.h";"bsl_iostream.h";"bsl_memory.h";"bsl_string.h";"bsl_type_traits.h";"bsl_variant.h"]

let mk_include s = str ("#include <" ^ s ^ ">")

let header fn () =
  let imps = get_custom_imports () in
  let himports = if Table.std_lib () = "BDE" then header_imports_bsl else header_imports in
  let himports = match fn with
  | Some s ->
    let s = Filename.basename s in
    (Filename.remove_extension s ^ ".h") :: himports
  | None -> himports in
  let h = List.fold_left (fun p s -> p ++ mk_include s ++ fnl ()) (str "") (himports @ imps) in
  if Table.std_lib () = "BDE"
  then h ++ fnl2() ++ str "namespace BloombergLP {" ++ fnl2() ++ str "}"
  else h ++ fnl2 ()

let spec_header () =
  let imps = get_custom_imports () in
  let himports = if Table.std_lib () = "BDE" then header_imports_bsl else header_imports in
  let h = List.fold_left (fun p s -> p ++ mk_include s ++ fnl ()) (str "") (himports @ imps) in
  (* let fun_concept = "template <typename F, typename Out, typename... In>\nconcept MapsTo = requires (const F &f, const In&... args) {\n{ f(args...) } -> std::same_as<Out>;\n};" in *)
  let fun_concept = if Table.std_lib () = "BDE"
 then "template <class From, class To>\nconcept convertible_to = bsl::is_convertible<From, To>::value;\n\ntemplate <class T, class U>\nconcept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;\n\ntemplate <class F, class R, class... Args>\nconcept MapsTo =\n requires (F& f, Args&... a) {\n { bsl::invoke(static_cast<F&>(f), static_cast<Args&>(a)...) }\n -> convertible_to<R>;\n };"
    else  "template <typename F, typename R, typename... Args>\nconcept MapsTo = std::is_invocable_r_v<R, F&, Args&...>;" in
  if Table.std_lib () = "BDE" then h ++ fnl2() ++ str "using namespace BloombergLP;" ++ fnl2 () ++ str fun_concept ++ fnl2()
  else h ++ fnl2 () ++ str fun_concept ++ fnl2() ++ str "template<class... Ts> struct Overloaded : Ts... { using Ts::operator()...; };\ntemplate<class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;" ++ fnl2 ()

let mono_filename f =
  let d = descr () in
  match f with
    | None -> None, None, default_id
    | Some f ->
        let f =
          if Filename.check_suffix f d.file_suffix then
            Filename.chop_suffix f d.file_suffix
          else f
        in
        let id =
          default_id
        in
        let f =
          if Filename.is_relative f then
            Filename.concat (output_directory_for_module ()) f
          else f
        in
        Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id

(* Builds a suitable filename from a module id *)

let module_filename mp =
  let f = file_of_modfile mp in
  let id = Id.of_string f in
  let f = Filename.concat (output_directory_for_module ()) f in
  let d = descr () in
  let fimpl_base = d.file_naming mp ^ d.file_suffix in
  let fimpl = Filename.concat (output_directory_for_module ()) fimpl_base in
  Some fimpl, Option.map ((^) f) d.sig_suffix, id

(*s Extraction of one decl to stdout. *)

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

(*s Extraction of a ml struct to a file. *)

(** For Recursive Extraction, writing directly on stdout
    won't work with rocqide, we use a buffer instead *)

let buf = Buffer.create 1000

let formatter dry file =
  let ft =
    if dry then Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    else
      match file with
        | Some f -> Topfmt.with_output_to f
        | None -> Format.formatter_of_buffer buf
  in
  (* XXX: Fixme, this shouldn't depend on Topfmt *)
  (* We never want to see ellipsis ... in extracted code *)
  Format.pp_set_max_boxes ft max_int;
  (* We reuse the width information given via "Set Printing Width" *)
  (match Topfmt.get_margin () with
    | None -> ()
    | Some i ->
      Format.pp_set_margin ft i;
      Format.pp_set_max_indent ft (i-10));
      (* note: max_indent should be < margin above, otherwise it's ignored *)
  ft

let get_comment () =
  let s = file_comment () in
  if String.is_empty s then None
  else
    let split_comment = Str.split (Str.regexp "[ \t\n]+") s in
    Some (prlist_with_sep spc str split_comment)

(* Helper to check if an executable is available in PATH *)
let executable_available exe =
  Sys.command ("which " ^ exe ^ " > /dev/null 2>&1") = 0

let rust_format_available () = executable_available "rustfmt"
let bde_format_available () = executable_available "bde-format"
let clang_format_available () = executable_available "clang-format"
let clang_available () = executable_available "clang"
let ocamlopt_available () = executable_available "ocamlopt"
let hyperfine_available () = executable_available "hyperfine"

(*
  [format_buffer_to_string buf] takes a buffer [buf],
  pipes its contents through {bde,clang}-format, and returns the formatted string.
  If {bde,clang}-format is not available or fails, it returns the original buffer contents.
*)
let format_buffer_to_string (buf : Buffer.t) : string =
  let use_bde = Table.format_style () = "BDE" in
  let formatter_cmd, available =
    if lang () == Cpp then
      if use_bde then "bde-format", bde_format_available ()
      else "clang-format -style=" ^ Filename.quote (Table.format_style ()), clang_format_available ()
    else "rustfmt", rust_format_available ()
  in
  if not available then (
    Feedback.msg_warning Pp.(str (if use_bde then "bde-format" else "clang-format") ++ spc () ++ str "not found: skipping formatting");
    Buffer.contents buf
  ) else
  let raw_output = Buffer.contents buf in
  match Unix.open_process_full formatter_cmd (Unix.environment ()) with
  | exception _ -> Buffer.contents buf
  | chan_in, chan_out, chan_err ->
      output_string chan_out raw_output;
      close_out chan_out;
      let fmt_buf = Buffer.create (Buffer.length buf) in
      (try
         while true do
           Buffer.add_string fmt_buf (input_line chan_in);
           Buffer.add_char fmt_buf '\n'
         done
       with End_of_file -> ());
      close_in chan_in;
      close_in chan_err;
      let status = Unix.close_process_full (chan_in, chan_out, chan_err) in
      match status with
      | Unix.WEXITED 0 -> Buffer.contents fmt_buf
      | _ -> Buffer.contents buf

(*
  [format_file_inplace filename] runs {bde,clang}-format -i on the given file [filename],
  formatting it in place. If {bde,clang}-format is not available, this is a no-op.
*)
let format_file_inplace (filename : string) : unit =
  let skip_format = Table.format_style () = "None" in
  let use_bde = Table.format_style () = "BDE" || Table.std_lib () = "BDE" in
  let available =
    if use_bde then bde_format_available ()
    else clang_format_available ()
  in
  if not available then
    Feedback.msg_warning Pp.(str (if use_bde then "bde-format" else "clang-format") ++ spc () ++ str "not found: skipping formatting")
  else
    let cmd =
      if use_bde then
        "bde-format -i " ^ Filename.quote filename
      else
        "clang-format -i -style=" ^ Filename.quote (Table.format_style ()) ^ " " ^ Filename.quote filename
    in
    if skip_format then () else
    ignore (Sys.command cmd)

let print_structure_to_file (fn,si,mo) dry struc =
  Buffer.clear buf;
  let d = descr () in
  reset_renaming_tables AllButExternal;
  let unsafe_needs = {
    mldummy = struct_ast_search Mlutil.isMLdummy struc;
    tdummy = struct_type_search Mlutil.isTdummy struc;
    tunknown = struct_type_search ((==) Tunknown) struc;
    magic = false }
  in
  (* First, a dry run, for computing objects to rename or duplicate *)
  set_phase Pre;
  ignore (d.pp_struct struc);
  let opened = opened_libraries () in
  (* Print the implementation *)
  let cout = if dry then None else Option.map open_out fn in
  let ft = formatter dry cout in
  let comment = get_comment () in
  begin try
    (* The real printing of the implementation *)
    set_phase Impl;
    pp_with ft (header fn ());
    pp_with ft (d.preamble mo comment opened unsafe_needs);
    pp_with ft (d.pp_struct struc);
    Format.pp_print_flush ft ();
    Option.iter close_out cout;
  with reraise ->
    Format.pp_print_flush ft ();
    Option.iter close_out cout; raise reraise
  end;
  (* If not a dry run, format the output file with clang-format *)
  if not dry then
    (Option.iter format_file_inplace fn;
     Option.iter info_file fn);
  (* Now, let's print the signature *)
  Option.iter
    (fun si ->
       let cout = open_out si in
       let ft = formatter false (Some cout) in
       begin try
         set_phase Intf;
         pp_with ft (spec_header ());
         pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
         pp_with ft (d.pp_hstruct struc);
         Format.pp_print_flush ft ();
         close_out cout;
       with reraise ->
         Format.pp_print_flush ft ();
         close_out cout; raise reraise
       end;
       (* Format the signature file with clang-format *)
       format_file_inplace si;
       info_file si)
    (if dry then None else si);
  (* Print the buffer content via Rocq standard formatter (ok with rocqide). *)
  if not (Int.equal (Buffer.length buf) 0) then begin
    let formatted_output = format_buffer_to_string buf in
    Feedback.msg_notice (str formatted_output);
    Buffer.reset buf
  end


(*********************************************)
(*s Part III: the actual extraction commands *)
(*********************************************)


let reset () =
  Visit.reset (); reset_tables (); reset_renaming_tables Everything

let init ?(compute=false) ?(inner=false) modular library =
  if not inner then check_inside_section ();
  set_keywords (descr ()).keywords;
  set_modular modular;
  set_library library;
  set_extrcompute compute;
  Cpp.reset_cpp_state ();  (* Reset ALL C++ global state from previous extractions *)
  reset ()

let warns () =
  warning_opaques (access_opaque ());
  warning_axioms ()

(* From a list of [reference], let's retrieve whether they correspond
   to modules or [global_reference]. Warn the user if both is possible. *)

let rec locate_ref = function
  | [] -> [],[]
  | qid::l ->
      let mpo = try Some (Nametab.locate_module qid) with Not_found -> None
      and ro =
        try Some (Smartlocate.global_with_alias qid)
        with Nametab.GlobalizationError _ | UserError _ -> None
      in
      match mpo, ro with
        | None, None -> Nametab.error_global_not_found ~info:Exninfo.null qid
        | None, Some r -> let refs,mps = locate_ref l in r::refs,mps
        | Some mp, None -> let refs,mps = locate_ref l in refs,mp::mps
        | Some mp, Some r ->
           warning_ambiguous_name ?loc:qid.CAst.loc (qid,mp,r);
           let refs,mps = locate_ref l in refs,mp::mps

(*s Recursive extraction in the Rocq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when
    extracting to a file with the command:
    \verb!Extraction "file"! [qualid1] ... [qualidn]. *)

let full_extr opaque_access f (refs,mps) =
  init false false;
  List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
  let struc = optimize_struct (refs,mps) (mono_environment ~opaque_access refs mps) in
  warns ();
  print_structure_to_file (mono_filename f) false struc;
  reset ()

let full_extraction ~opaque_access f lr =
  full_extr opaque_access f (locate_ref lr)

(*s Separate extraction is similar to recursive extraction, with the output
   decomposed in many files, one per Rocq .v file *)

let separate_extraction ~opaque_access lr =
  init true false;
  let refs,mps = locate_ref lr in
  let struc = optimize_struct (refs,mps) (mono_environment ~opaque_access refs mps) in
  let () = List.iter (function
    | MPfile _, _ -> ()
    | (MPdot _ | MPbound _), _ ->
      user_err (str "Separate Extraction from inside a module is not supported."))
      struc
  in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
        print_structure_to_file (module_filename mp) false [e]
    | (MPdot _ | MPbound _), _ -> assert false
  in
  List.iter print struc;
  reset ()

(*s Simple extraction in the Rocq toplevel. The vernacular command
    is \verb!Extraction! [qualid]. *)

let simple_extraction ~opaque_access r =
  match locate_ref [r] with
  | ([], [mp]) as p -> full_extr opaque_access None p
  | [r],[] ->
      init false false;
      let struc = optimize_struct ([r],[]) (mono_environment ~opaque_access [r] []) in
      let d = get_decl_in_structure r struc in
      warns ();
      let flag =
        if is_any_custom r then str "/* User defined extraction */" ++ fnl()
        else mt ()
      in
      let ans = flag ++ print_one_decl struc (modpath_of_r r) d in
      reset ();
      Feedback.msg_notice ans
  | _ -> assert false


(*s (Recursive) Extraction of a library. The vernacular command is
  \verb!(Recursive) Extraction Library! [M]. *)

let extraction_library ~opaque_access is_rec CAst.{loc;v=m} =
  init true true;
  let dir_m =
    let q = qualid_of_ident m in
    try Nametab.full_name_module q with Not_found -> error_unknown_module ?loc q
  in
  Visit.add_mp_all (MPfile dir_m);
  let env = Global.env () in
  let l = List.rev (environment_until (Some dir_m)) in
  let select l (mp,struc) =
    if Visit.needed_mp mp
    then (mp, extract_structure opaque_access env mp no_delta ~all:true struc) :: l
    else l
  in
  let struc = List.fold_left select [] l in
  let struc = optimize_struct ([],[]) struc in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
        let dry = not is_rec && not (DirPath.equal dir dir_m) in
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
  try ignore (Sys.getenv "INSIDE_DUNE"); true
  with Not_found -> false

(* Helper to emit structured test output for dune.
   Format: CRANE_TEST:STATUS:test_name:source_file
   where STATUS is one of: PASS, FAIL_TEST, FAIL_COMPILE, FAIL_EXTRACT
   This single-line format avoids the multi-line parsing issues we had before. *)
let emit_test_status status test_id_str source_file =
  Feedback.msg_notice Pp.(str "CRANE_TEST:" ++ str status ++ str ":" ++ str test_id_str ++ str ":" ++ str source_file)

(* Helper to derive source .v file from output directory.
   During extraction, we write to paths like:
     _build/default/../../tests/basics/nat/nat.cpp
   This function finds the corresponding .v file in that directory and
   cleans up the path to be relative to project root (e.g., tests/basics/nat/Nat.v).
   Returns empty string if we can't determine the source file uniquely. *)
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
        else full_path
      in
      (* Resolve remaining ../ and ./ references by walking the path components *)
      let parts = String.split_on_char '/' cleaned in
      let rec resolve acc = function
        | [] -> List.rev acc
        | ".." :: rest ->
          (* Go up one directory by popping from accumulator *)
          (match acc with _ :: tail -> resolve tail rest | [] -> resolve acc rest)
        | "." :: rest -> resolve acc rest
        | part :: rest -> resolve (part :: acc) rest
      in
      let resolved = String.concat "/" (resolve [] parts) in
      (* If still absolute, make relative to current working directory *)
      if String.length resolved > 0 && resolved.[0] = '/' then
        let cwd = Sys.getcwd () in
        if String.starts_with ~prefix:(cwd ^ "/") resolved then
          String.sub resolved (String.length cwd + 1) (String.length resolved - String.length cwd - 1)
        else resolved
      else resolved
    | _ -> ""  (* Not exactly one .v file - can't determine source uniquely *)
  with _ -> ""

(* For the test-suite :
   extraction to a temporary file + run clang on it *)

exception NoClangFound
exception ClangError of int * string

let compile_cpp ?(shouldlink=false) ?(includes=[]) ?outfile ?errfile infile =
  if not (clang_available ()) then raise NoClangFound;
  let errfile =
    match errfile with
    | Some e -> e
    | None -> Filename.temp_file ("cpp_" ^ Filename.basename infile ^ "_error") ".log" in
  let outfile = match outfile with Some o -> o | None -> Filename.chop_suffix infile ".cpp" ^ (if shouldlink then "" else ".o") in
  let args = if Table.std_lib () = "BDE"
    then
      let bde_dir =
        let n = String.length (Table.bde_dir ()) in
        if n > 0 && (Table.bde_dir ()).[n - 1] = '/' then
          String.sub (Table.bde_dir ()) 0 (n - 1)
        else Table.bde_dir () in
      [ "clang++"
             ] @ (prepend_to_all "-I" includes) @
             [ if shouldlink then "" else "-c"
             ; "-std=c++20"
             ; "-Wno-deprecated-literal-operator"
             ; "-Wno-unused-command-line-argument"
             ; "-I" ; bde_dir ^ "/include"
             ; infile
             ; "-L"; bde_dir ^ "/lib"
             ; "-lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2"
             ; "-o"; outfile
             ; "2>" ; errfile
             ]
    else [ "clang++"
             ] @ (prepend_to_all "-I" includes) @
             [ if shouldlink then "" else "-c"
             ; "-std=c++23"
             ; infile
             ; "-o"; outfile
             ; "2>" ; errfile
             ] in
  let cmd = String.concat " " args in
  let res = Sys.command cmd in
  if res <> 0 then (
    let ic = open_in errfile in
    let errors = really_input_string ic (in_channel_length ic) in
    close_in ic;
    if Sys.file_exists errfile then Sys.remove errfile;
    raise (ClangError (res, errors))
  );
  if Sys.file_exists errfile then Sys.remove errfile


exception NoOcamloptFound
exception OcamloptError of int * string

let compile_ocaml ?(shouldlink=false) ?(includes=[]) ?outfile ?errfile infile =
  if not (ocamlopt_available ()) then raise NoOcamloptFound;
  let errfile =
    match errfile with
    | Some e -> e
    | None -> Filename.temp_file ("ocaml_" ^ Filename.basename infile ^ "_error") ".log" in
  let outfile = match outfile with Some o -> o | None -> Filename.chop_suffix infile ".ml" in
  let args = [ Envars.ocamlfind ()
             ; "ocamlopt"
             ] @ (prepend_to_all "-I" includes) @
             [ if shouldlink then "" else "-c"
             ; "-o"; outfile
             ; infile
             ; "2>" ; errfile ] in
  let cmd = String.concat " " args in
  let res = Sys.command cmd in
  if res <> 0 then (
    let ic = open_in errfile in
    let errors = really_input_string ic (in_channel_length ic) in
    close_in ic;
    if Sys.file_exists errfile then Sys.remove errfile;
    raise (OcamloptError (res, errors))
  );
  if Sys.file_exists errfile then Sys.remove errfile

let compile_and_test ?outfile ?errfile infile =
  if not (clang_available ()) then raise NoClangFound;
  let dir = Filename.dirname infile in
  let errfile =
    match errfile with
    | Some e -> e
    | None -> Filename.temp_file ("cpp_" ^ Filename.basename infile ^ "_error") ".log" in
  let ofile = match outfile with Some o -> o | None -> Filename.chop_suffix infile ".cpp" ^ ".t.exe" in
  let args = if Table.std_lib () = "BDE"
    then
      let bde_dir =
        let n = String.length (Table.bde_dir ()) in
        if n > 0 && (Table.bde_dir ()).[n - 1] = '/' then
          String.sub (Table.bde_dir ()) 0 (n - 1)
        else Table.bde_dir () in
      [ "clang++"
             ; "-O2"
             ; "-std=c++20"
             ; "-Wno-deprecated-literal-operator"
             ; "-Wno-unused-command-line-argument"
             ; "-I" ; dir
             ; "-I" ; bde_dir ^ "/include"
             ; Filename.chop_suffix infile ".cpp" ^ ".o"
             ; Filename.chop_suffix infile ".cpp" ^ ".t.cpp"
             ; "-L" ; bde_dir ^ "/lib"
             ; "-lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2"
             ; "-o"; ofile
             ; "2>" ; errfile
             ]
    else [ "clang++"
             ; "-O2"
             ; "-std=c++23"
             ; "-I" ; dir
             ; Filename.chop_suffix infile ".cpp" ^ ".o"
             ; Filename.chop_suffix infile ".cpp" ^ ".t.cpp"
             ; "-o"; ofile
             ; "2>" ; errfile
             ] in
  let cmd = String.concat " " args in
  let res = Sys.command cmd in
  if res <> 0 then (
    let ic = open_in errfile in
    let errors = really_input_string ic (in_channel_length ic) in
    close_in ic;
    if Sys.file_exists errfile then Sys.remove errfile;
    raise (ClangError (res, errors))
  );
  if Sys.file_exists errfile then Sys.remove errfile;
  let out = Filename.temp_file "test_out" ".log" in
  let test_exit_code = Sys.command (ofile ^ " >" ^ out ^ " 2>&1") in
  let ic = open_in out in
  let out_string = really_input_string ic (in_channel_length ic) in
  close_in ic;
  if Sys.file_exists out then Sys.remove out;
  (* If test returns non-zero, it failed *)
  if test_exit_code <> 0 then
    raise (Failure ("Test assertions failed (exit code " ^ string_of_int test_exit_code ^ ")"));
  out_string

let extract_and_compile ~opaque_access file l =
  let filename =
    match mono_filename file with
    | (Some fn, _, _) ->
      let dir = Filename.concat (Filename.dirname fn) (Filename.remove_extension (Filename.basename fn)) in
      Filename.concat dir (Filename.basename fn)
    | (None, _, _) -> Filename.temp_file "testextraction" ".cpp" in
  (* Build test identifier like "nat/Nat" for display *)
  let output_name = Filename.remove_extension (Filename.basename filename) in
  let test_id = Pp.(str output_name ++ str "/" ++ pr_enum Libnames.pr_qualid l) in
  let test_id_str = Pp.string_of_ppcmds test_id in
  (* Check if we're running in dune test mode - determines output format *)
  let in_dune = is_running_in_dune () in
  (* For dune, derive the source .v file path for structured output.
     For interactive use (Proof General, VSCode), we don't need this. *)
  let source_file = if in_dune then derive_source_file filename else "" in
  (* Phase 1: Extract Rocq definitions to C++ code *)
  let extraction_ok =
    try full_extraction ~opaque_access (Some filename) l; true
    with exn ->
      (* Emit structured output for dune, or pretty error for interactive use *)
      if in_dune then
        emit_test_status "FAIL_EXTRACT" test_id_str source_file
      else
        ignore (CErrors.user_err Pp.(test_id ++ spc () ++ str "failed to extract:"
          ++ fnl () ++ str (Printexc.to_string exn) ++ fnl () ++ str (Printexc.get_backtrace ())));
      false
  in
  if extraction_ok then (
    format_file_inplace filename;
    (* Phase 2: Compile the generated C++ code with clang *)
    let compilation_ok =
      try compile_cpp ~includes:[Filename.dirname filename] filename; true
      with
      | NoClangFound ->
        if in_dune then emit_test_status "FAIL_COMPILE" test_id_str source_file
        else ignore (CErrors.user_err Pp.(test_id ++ spc () ++ str "extracted but clang cannot be found."));
        false
      | ClangError(_exit_code, clang_errors) ->
        if in_dune then emit_test_status "FAIL_COMPILE" test_id_str source_file
        else ignore (CErrors.user_err (if !Flags.quiet then
          Pp.(test_id ++ spc () ++ str "extracted but clang failed to compile.")
        else
          Pp.(test_id ++ spc () ++ str "extracted but clang failed to compile with:" ++ fnl () ++ str clang_errors)));
        false
      | exn ->
        if in_dune then emit_test_status "FAIL_COMPILE" test_id_str source_file
        else ignore (CErrors.user_err (if !Flags.quiet then
          Pp.(test_id ++ spc () ++ str "extracted but failed to compile.")
        else
          Pp.(test_id ++ spc () ++ str "extracted but failed to compile:" ++ fnl () ++ str (Printexc.to_string exn))));
        false
    in
    (* Phase 3: Run test assertions (if any) embedded in the .v file *)
    let (tests_ok, out) = try let o = compile_and_test filename in (true, o)
                   with _ -> (false, "") in
    let base = Filename.chop_suffix filename ".cpp" in
    (* Clean up temporary files if this was a temp extraction *)
    if not (Option.has_some file) then
      (if Sys.file_exists filename then Sys.remove filename;
       if Sys.file_exists base then Sys.remove base);
    (* Report final status: structured for dune, pretty for interactive *)
    if compilation_ok && tests_ok then
      Feedback.msg_notice (if in_dune then
        Pp.(str "CRANE_TEST:PASS:" ++ str test_id_str ++ str ":" ++ str source_file)
      else
        Pp.(str "✅ " ++ test_id ++ spc () ++ str "successfully extracted, compiled, and all tests passed."
            ++ (if !Flags.quiet || Option.is_empty file then mt () else spc () ++ str "(" ++ str filename ++ str ")")
            ++ fnl () ++ str out ++ fnl ()));
    if compilation_ok && not tests_ok then
      Feedback.msg_notice (if in_dune then
        Pp.(str "CRANE_TEST:FAIL_TEST:" ++ str test_id_str ++ str ":" ++ str source_file)
      else
        Pp.(str "❌ " ++ test_id ++ spc () ++ str "extracted and compiled, but test assertions failed."
            ++ (if !Flags.quiet || Option.is_empty file then mt () else spc () ++ str "(" ++ str filename ++ str ")")
            ++ fnl ()));

  )

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

(* Replace paths of the compiled executables with user-readable descriptions of each benchmark *)
let replace_paths_with_names execs output =
  List.fold_right (fun (i, desc, tmpfile, outfile) ->
    let name = "Benchmark " ^ string_of_int i in
    let once = ref false in
    Str.global_substitute
      (Str.regexp ("\\(" ^ Str.quote outfile ^ "\\)"))
      (fun _ -> if !once then name else (once := true; name ^ " (" ^ desc ^ ")"))) execs output

(* Hyperfine has its own count of benchmarks since we do not pass it the ones that didn't compile.
   But we still want to keep the user-provided numbering of the benchmarks.
   It is better if we remove the numbering part of the Hyperfine output
   and add that in the user-readable description. *)
let clean_benchmark_lines output =
  let benchmark_re = Str.regexp "^\\(Benchmark [0-9]+: \\)" in
  Str.global_substitute benchmark_re (fun _ -> "") output

let benchmark term options =
  if not (hyperfine_available ()) then
    CErrors.user_err Pp.(str "Hyperfine is not available: cannot run benchmarks.");
  (* Type check: term must have type unit -> string *)
  begin
    let open Names in
    let open Constr in
    let open Globnames in
    let open Environ in
    let open Evd in
    let open Libnames in
    let open Reductionops in
    let open Pp in
    let env = Global.env () in
    let sigma = Evd.from_env env in

    (* Step 1: Locate the global reference from the qualid *)
    let gr = Smartlocate.global_with_alias term in
    let econstr =
      match gr with
      (* Step 2: Ensure it's a constant *)
      | GlobRef.ConstRef c ->
        let cb = Global.lookup_constant c in
        (match cb.const_body with
         | Def body -> EConstr.of_constr body
         | _ -> CErrors.user_err (str "Cannot extract body from constant"))
      | _ -> CErrors.user_err (str "Only constant references are supported for benchmarking")
    in
    (* Step 3: Get the type of the constant *)
    let actual_ty = snd (Typing.type_of env sigma econstr) in

    (* Step 4: Construct the expected type: unit -> string *)
    let locate_type path =
      let gr = Nametab.locate (Libnames.qualid_of_string path) in
      match gr with
      | GlobRef.ConstRef c -> Constr.mkConstU (c, UVars.Instance.empty)
      | GlobRef.IndRef (ind, _) -> Constr.mkIndU ((ind, 0), UVars.Instance.empty)
      | GlobRef.ConstructRef ((ind, idx), _) -> Constr.mkConstructU (((ind, 0), idx), UVars.Instance.empty)
      | _ -> CErrors.user_err (str "Expected a constant, inductive, or constructor reference for type location")
    in

    let unit_ty = locate_type "Corelib.Init.Datatypes.unit" in
    let string_ty = locate_type "Corelib.Strings.PrimString.string" in
    let expected_ty = Term.mkArrow unit_ty Sorts.Relevant string_ty in

    (* Step 5: Compare actual and expected types *)
    let evd = Evd.from_env env in
    if not (is_conv env evd actual_ty (EConstr.of_constr expected_ty)) then
      let actual_ty_pp = Printer.pr_econstr_env env evd actual_ty in
      let expected_ty_pp = Printer.pr_constr_env env evd expected_ty in
      CErrors.user_err
        (str "Benchmark term '" ++ Libnames.pr_qualid term ++ str "' has the wrong type:"
          ++ fnl () ++ str "Actual type: " ++ actual_ty_pp
          ++ fnl () ++ str "Expected type: " ++ expected_ty_pp)
  end;
  (* Start compiling based on user-provided options *)
  let execs =
    List.mapi (fun i (lang, file, flags) ->
      let i = i + 1 in (* use 1-indexing since this is user-facing *)
      let file = Filename.concat (output_directory ()) file in
      (* Generate a temporary input file to append the driver *)
      let tmpfile = Filename.temp_file "benchmark" (match lang with BenchmarkCpp -> ".cpp" | BenchmarkOCaml -> ".ml") in
      let in_chan = open_in file in
      let out_chan = open_out tmpfile in
      (try while true do output_string out_chan (input_line in_chan ^ "\n") done with End_of_file -> ());
      close_in in_chan;
      (* Append the driver code *)
      let main_code = match lang with
        | BenchmarkCpp ->
          "\nint main() {\n  std::cout << (" ^ Libnames.string_of_qualid term ^ " (unit::tt::make())) << std::endl;\n  return 0;\n}\n"
        | BenchmarkOCaml ->
          "\nlet () = print_endline (" ^ Libnames.string_of_qualid term ^ " ())\n"
      in
      output_string out_chan main_code;
      close_out out_chan;
      let outfile = Filename.concat (output_directory ()) ("benchmark_output_" ^ string_of_int i ^ ".out") in
      match lang with
      | BenchmarkCpp ->
        (try
           compile_cpp ~shouldlink:true ~includes:[Filename.dirname file] ~outfile tmpfile;
           (* Feedback.msg_notice (str ("Compiled: " ^ tmp_file ^ " -> " ^ outfile)); *)
           let desc = "extraction via Crane to C++, compiled via Clang" ^
                      if String.is_empty flags then "" else " with options " ^ flags in
           Some (i, desc, tmpfile, outfile)
         with NoClangFound -> Feedback.msg_warning (str ("clang not found")); None
            | ClangError (_, msg) -> Feedback.msg_warning (str msg); None
            | _ -> Feedback.msg_warning (str ("Failed to compile: " ^ tmpfile)); None)
      | BenchmarkOCaml ->
        (try
           compile_ocaml ~shouldlink:true ~includes:[Filename.dirname file] ~outfile tmpfile;
           (* Feedback.msg_notice (str ("Compiled: " ^ tmp_file ^ " -> " ^ outfile)); *)
           let desc = "built-in extraction to OCaml, compiled via ocamlopt" ^
                      if String.is_empty flags then "" else " with options " ^ flags in
           Some (i, desc, tmpfile, outfile)
         with NoOcamloptFound -> Feedback.msg_warning (str ("ocamlopt not found")); None
            | OcamloptError (_, msg) -> Feedback.msg_warning (str msg); None
            | _ -> Feedback.msg_warning (str ("Failed to compile: " ^ tmpfile)); None)
    ) options
    |> List.filter_map (fun x -> x) (* Don't pass noncompiling benchmarks to Hyperfine *)
  in
  if execs <> [] then
    let cmd = "hyperfine --style=basic " ^
              String.concat " " (List.map (fun (_,_,_,outfile) -> outfile) execs) ^ " 2> /dev/null" in
    (* Feedback.msg_info (str cmd); *)
    let ic = Unix.open_process_in cmd in
    let buf = Buffer.create 1024 in
    (try while true do Buffer.add_string buf (input_line ic ^ "\n") done with End_of_file -> ());
    let _ = Unix.close_process_in ic in
    Buffer.contents buf
      |> clean_benchmark_lines
      |> replace_paths_with_names execs
      |> str |> Feedback.msg_info;
    (* Delete temporary files and compiled executables *)
    List.iter (fun (_,_,tmpfile,outfile) ->
      if Sys.file_exists outfile then Sys.remove outfile;
      if Sys.file_exists tmpfile then Sys.remove tmpfile) execs
