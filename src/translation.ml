(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Conversion functions from Miniml to Minicpp types *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Str
open Util

exception TODO

(* Mutable context tracking inductives defined in the current module scope.
   When set, references to these inductives won't be wrapped in Tnamespace,
   so they appear as sibling types rather than outer-namespace-qualified types. *)
let local_inductives : GlobRef.t list ref = ref []

let add_local_inductive (r : GlobRef.t) =
  local_inductives := r :: !local_inductives

let clear_local_inductives () =
  local_inductives := []

let get_local_inductives () =
  !local_inductives

(* Helper to create CPPglob with pre-computed custom_info *)
let mk_cppglob (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  let ci = {
    ci_inline = (if Table.to_inline r then Table.find_custom_opt r else None);
    ci_is_custom = Table.is_custom r;
  } in
  CPPglob (r, tys, Some ci)

(* Helper for local variables (VarRef) - no custom extraction applies *)
let mk_cppglob_local (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  CPPglob (r, tys, None)

(* ========================================================================== *)
(*  Translation context — consolidated mutable state for expression compilation.
    All fields except local_inductives (which has a different lifecycle and is
    exported to cpp.ml) are grouped here in a single mutable record.        *)
(* ========================================================================== *)

type translation_ctx = {
  mutable current_type_vars : Id.t list;
  mutable current_param_types : (int * ml_type) list;
  mutable current_outer_function_name : string option;
  (* C++ return type of the enclosing function, set by gen_dfun.
     Used to recover erased template type args at call sites
     where C++ can't deduce them from lambda arguments. *)
  mutable current_cpp_return_type : cpp_type option;
  mutable env_types : (Id.t * ml_type) list;
  mutable pending_lifted_decls : cpp_decl list;
  mutable unique_bindings : int list;
  mutable current_letin_depth : int;
  mutable move_owned_vars : Escape.IntSet.t;
  mutable move_dead_after : Escape.IntSet.t;
  mutable move_n_params : int;
}

let tctx = {
  current_type_vars = [];
  current_param_types = [];
  current_outer_function_name = None;
  current_cpp_return_type = None;
  env_types = [];
  pending_lifted_decls = [];
  unique_bindings = [];
  current_letin_depth = 0;
  move_owned_vars = Escape.IntSet.empty;
  move_dead_after = Escape.IntSet.empty;
  move_n_params = 0;
}

(* Accessor wrappers — thin layer over tctx fields. *)
let set_current_type_vars (tvars : Id.t list) =
  tctx.current_type_vars <- tvars
let get_current_type_vars () = tctx.current_type_vars
let clear_current_type_vars () =
  tctx.current_type_vars <- []

let set_current_param_types (params : (Id.t * ml_type) list) =
  tctx.current_param_types <- List.mapi (fun i (_, ty) ->
    (i + 1, ty)) params
let get_param_type_by_index (idx : int) : ml_type option =
  try Some (List.assoc idx tctx.current_param_types)
  with Not_found -> None
let clear_current_param_types () =
  tctx.current_param_types <- []

let add_lifted_decl (d : cpp_decl) =
  tctx.pending_lifted_decls <- d :: tctx.pending_lifted_decls
let take_lifted_decls () =
  let ds = List.rev tctx.pending_lifted_decls in
  tctx.pending_lifted_decls <- []; ds

let push_env_types (ids : (Id.t * ml_type) list) =
  tctx.env_types <- ids @ tctx.env_types
let get_env_type (i : int) : ml_type = snd (List.nth tctx.env_types (pred i))
let reset_env_types () = tctx.env_types <- []

let ml_type_is_void : ml_type -> bool = function
| Tglob (r, _, _) -> is_void r
| _ -> false

(* Run escape analysis on [body], saving and restoring the analysis state
   around the call to [f]. This is needed because escape analysis runs at
   multiple nesting levels (lambdas, let-in expressions, top-level functions)
   and each level has its own set of safe bindings. *)
let with_escape_analysis body f =
  let saved_ub = tctx.unique_bindings in
  let saved_depth = tctx.current_letin_depth in
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  tctx.unique_bindings <- Escape.analyze body;
  tctx.current_letin_depth <- 0;
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_owned_vars <- Escape.IntSet.empty;
  tctx.move_n_params <- 0;
  let result = f () in
  tctx.unique_bindings <- saved_ub;
  tctx.current_letin_depth <- saved_depth;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  result

(* Swap shared_ptr to unique_ptr in a C++ type. *)
let shared_to_unique = function
  | Tshared_ptr inner -> Tunique_ptr inner
  | other -> other

(* Swap shared_ptr construction to unique_ptr construction in a C++ expression.
   Handles three patterns:
   1. shared_ptr<T>(expr) -> unique_ptr<T>(expr)
   2. make_shared<T>(args) -> make_unique<T>(args)
   3. Type::ctor::Cons_(args) -> Type::ctor::Cons_uptr(args)
      Redirects to the unique_ptr factory variant generated in the struct. *)
let shared_expr_to_unique = function
  | CPPshared_ptr_ctor (ty, e) -> CPPunique_ptr_ctor (ty, e)
  | CPPfun_call (CPPmk_shared ty, args) -> CPPfun_call (CPPmk_unique ty, args)
  | CPPfun_call (CPPqualified (CPPqualified (type_expr, ctor_id), factory_id), args)
    when Names.Id.to_string ctor_id = "ctor" ->
      let factory_str = Names.Id.to_string factory_id in
      let uptr_name = String.sub factory_str 0 (String.length factory_str - 1) ^ "_uptr" in
      CPPfun_call (CPPqualified (CPPqualified (type_expr, ctor_id), Names.Id.of_string uptr_name), args)
  | e -> e

(* ============================================================================
   Shared helpers for method generation (used by gen_ind_header_v2 and gen_record_methods)
   ============================================================================ *)

module IntSet = Escape.IntSet

(* Collect all Tvar indices from an ml_type.
   Used to find type variables beyond those of the containing inductive/record. *)
let rec collect_tvars_set acc = function
  | Miniml.Tvar i | Miniml.Tvar' i -> IntSet.add i acc
  | Miniml.Tarr (t1, t2) -> collect_tvars_set (collect_tvars_set acc t1) t2
  | Miniml.Tglob (_, args, _) -> List.fold_left collect_tvars_set acc args
  | Miniml.Tmeta { contents = Some t } -> collect_tvars_set acc t
  | _ -> acc

let collect_tvars acc ty =
  IntSet.elements (collect_tvars_set (IntSet.of_list acc) ty)

(* Check if a C++ type is a dummy type glob (e.g., dummy_type, dummy_prop, dummy_implicit).
   These arise from Tdummy Ktype/Kprop/Kimplicit in the ML AST, which
   convert_ml_type_to_cpp_type maps to Tglob(VarRef "dummy_type") etc.  These
   intermediate markers are used by the filtering pipeline (gen_expr, eta_fun,
   gen_decl_for_pp) to detect erased parameters and drop them before they reach
   the C++ renderer — they should never appear in the final generated output. *)
let is_cpp_dummy_type = function
  | Minicpp.Tglob (GlobRef.VarRef id, [], _) ->
      let name = Id.to_string id in
      name = "dummy_type" || name = "dummy_prop" || name = "dummy_implicit"
  | _ -> false

(* True if a C++ type represents an erased parameter — either Tany (from an
   unresolved Tmeta in the ML AST) or a dummy_type glob (from Tdummy).  When
   any type arg in a template argument list is erased, ALL explicit type args
   must be dropped (see filter_erased_type_args). *)
let is_erased_type t = t = Minicpp.Tany || is_cpp_dummy_type t

(* If any type arg is erased (Tany or dummy_type), drop ALL explicit type args
   and let the C++ compiler deduce everything.  We must drop ALL args (not just
   the erased ones) because C++ template arguments are positional: removing only
   the erased slots would shift the remaining args into the wrong positions,
   causing type mismatches.  Dropping all args is safe because C++ can deduce
   them from the call-site argument types. *)
let filter_erased_type_args tys =
  if List.exists is_erased_type tys then [] else tys

(* Recursively check whether a C++ type tree contains erased HKT markers
   (Tany or dummy_type globs).  These markers arise when a higher-kinded type
   constructor (e.g., F : Type -> Type) is erased during extraction — the
   type constructor itself becomes Tany/dummy_type, but it may be nested inside
   a function type like (A -> B) -> F A -> F B.  Used by gen_dfun and
   gen_decl_for_pp to detect function params whose type variables cannot be
   deduced by C++ and should therefore use plain TTtypename instead of a
   MapsTo constraint. *)
let rec has_hkt_erasure = function
  | Minicpp.Tany -> true
  | t when is_cpp_dummy_type t -> true
  | Minicpp.Tfun (d, c) -> List.exists has_hkt_erasure d || has_hkt_erasure c
  | Minicpp.Tmod (_, t) | Minicpp.Tref t | Minicpp.Tshared_ptr t
  | Minicpp.Tunique_ptr t | Minicpp.Tnamespace (_, t) -> has_hkt_erasure t
  | Minicpp.Tglob (_, ts, _) | Minicpp.Tvariant ts ->
      List.exists has_hkt_erasure ts
  | _ -> false

(* Collect all Tvar indices from an ML AST, using collect_tvars on embedded types. *)
let rec collect_tvars_ast acc = function
  | MLlam (_, ty, body) -> collect_tvars_ast (collect_tvars acc ty) body
  | MLletin (_, ty, a, b) -> collect_tvars_ast (collect_tvars_ast (collect_tvars acc ty) a) b
  | MLglob (_, tys) -> List.fold_left collect_tvars acc tys
  | MLcons (ty, _, args) -> List.fold_left collect_tvars_ast (collect_tvars acc ty) args
  | MLcase (ty, e, brs) ->
      let acc = collect_tvars_ast (collect_tvars acc ty) e in
      Array.fold_left (fun acc (ids, ty, _, body) ->
        let acc = List.fold_left (fun acc (_, t) -> collect_tvars acc t) acc ids in
        collect_tvars_ast (collect_tvars acc ty) body) acc brs
  | MLfix (_, ids, funs, _) ->
      let acc = Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) acc ids in
      Array.fold_left collect_tvars_ast acc funs
  | MLapp (f, args) -> List.fold_left collect_tvars_ast (collect_tvars_ast acc f) args
  | MLmagic a -> collect_tvars_ast acc a
  | MLparray (arr, def) -> collect_tvars_ast (Array.fold_left collect_tvars_ast acc arr) def
  | MLtuple args -> List.fold_left collect_tvars_ast acc args
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> acc

(* Check if an ML type contains any unresolved type variable or placeholder.
   Returns true for Tvar, Tvar', unresolved Tmeta, and Tunknown.
   Used to guard Tvar substitution: we only substitute with fully concrete types. *)
let rec has_tvar = function
  | Miniml.Tvar _ | Miniml.Tvar' _ -> true
  | Miniml.Tunknown -> true
  | Miniml.Tarr (t1, t2) -> has_tvar t1 || has_tvar t2
  | Miniml.Tglob (_, args, _) -> List.exists has_tvar args
  | Miniml.Tmeta { contents = Some t } -> has_tvar t
  | Miniml.Tmeta { contents = None } -> true
  | _ -> false

(* Apply a type-level transformation to every type annotation in an ML AST. *)
let rec map_types_in_ast (f : ml_type -> ml_type) = function
  | MLlam (id, ty, body) ->
    MLlam (id, f ty, map_types_in_ast f body)
  | MLletin (id, ty, a, b) ->
    MLletin (id, f ty, map_types_in_ast f a, map_types_in_ast f b)
  | MLglob (r, tys) -> MLglob (r, List.map f tys)
  | MLcons (ty, r, args) ->
    MLcons (f ty, r, List.map (map_types_in_ast f) args)
  | MLcase (ty, e, brs) ->
    MLcase (f ty, map_types_in_ast f e,
      Array.map (fun (ids, ty, pat, body) ->
        (List.map (fun (id, t) -> (id, f t)) ids,
         f ty, pat, map_types_in_ast f body)) brs)
  | MLfix (i, ids, funs, cf) ->
    MLfix (i, Array.map (fun (n, ty) -> (n, f ty)) ids,
           Array.map (map_types_in_ast f) funs, cf)
  | MLapp (fn, args) ->
    MLapp (map_types_in_ast f fn, List.map (map_types_in_ast f) args)
  | MLmagic a -> MLmagic (map_types_in_ast f a)
  | MLparray (arr, def) ->
    MLparray (Array.map (map_types_in_ast f) arr, map_types_in_ast f def)
  | MLtuple args -> MLtuple (List.map (map_types_in_ast f) args)
  | (MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _
    | MLfloat _ | MLstring _) as t -> t

(* Build Tvar i -> concrete_type substitution by unifying two ML types structurally.
   Walks both types in parallel; when one side has Tvar i and the other has a concrete
   type, records the mapping. Conflicting mappings are discarded. *)
let build_tvar_subst_from_unify ty_with_tvars ty_concrete =
  let seen = Hashtbl.create 8 in
  let rec unify t1 t2 = match t1, t2 with
    | (Miniml.Tvar i | Miniml.Tvar' i), _ when not (has_tvar t2) ->
      (match Hashtbl.find_opt seen i with
       | None -> Hashtbl.replace seen i (Some t2)
       | Some (Some _) -> Hashtbl.replace seen i None
       | Some None -> ())
    | _, (Miniml.Tvar i | Miniml.Tvar' i) when not (has_tvar t1) ->
      (match Hashtbl.find_opt seen i with
       | None -> Hashtbl.replace seen i (Some t1)
       | Some (Some _) -> Hashtbl.replace seen i None
       | Some None -> ())
    | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) -> unify a1 a2; unify b1 b2
    | Miniml.Tglob (_, args1, _), Miniml.Tglob (_, args2, _)
      when List.length args1 = List.length args2 ->
      List.iter2 unify args1 args2
    | Miniml.Tmeta { contents = Some t }, other
    | other, Miniml.Tmeta { contents = Some t } -> unify t other
    | _ -> ()
  in
  unify ty_with_tvars ty_concrete;
  Hashtbl.fold (fun i v acc -> match v with Some ty -> (i, ty) :: acc | None -> acc) seen []

(* Collect all types that should be unified with the top-level function type.
   Returns a list of types to unify pairwise with the top-level type:
   - The arrow type reconstructed from MLlam annotations
   - The type annotation on the MLfix binding (if present)
   - The arrow type from the MLfix's inner function body *)
let collect_body_types_for_unify body =
  let types = ref [] in
  let rec from_lams = function
    | MLlam (_, ty, inner) -> Miniml.Tarr (ty, from_lams inner)
    | MLfix (_, ids, funs, _) ->
      Array.iter (fun (_, ty) -> types := ty :: !types) ids;
      Array.iter (fun f -> types := from_lams f :: !types) funs;
      Miniml.Tunknown
    | _ -> Miniml.Tunknown
  in
  let outer = from_lams body in
  outer :: !types

(* Apply a Tvar substitution to an ML type. *)
let rec subst_tvars_type subst = function
  | Miniml.Tvar i | Miniml.Tvar' i ->
    (match List.assoc_opt i subst with Some t -> t | None -> Miniml.Tvar i)
  | Miniml.Tarr (a, b) -> Miniml.Tarr (subst_tvars_type subst a, subst_tvars_type subst b)
  | Miniml.Tglob (r, args, a) -> Miniml.Tglob (r, List.map (subst_tvars_type subst) args, a)
  | Miniml.Tmeta {contents = Some t} -> subst_tvars_type subst t
  | t -> t

(* Resolve Tvars in the body by unifying body type annotations with the top-level type.
   Only applied when the top-level type is fully concrete (no Tvars, no unresolved metas).
   Returns the (possibly substituted) body. *)
let resolve_body_tvars b ty =
  let ty = type_simpl ty in
  if has_tvar ty then b  (* top-level type is polymorphic, don't touch the body *)
  else
    let body_types = collect_body_types_for_unify b in
    let tvar_subst = List.concat_map (fun bt -> build_tvar_subst_from_unify bt ty) body_types in
    let tvar_subst = List.fold_left (fun acc (i, t) ->
      if List.mem_assoc i acc then acc else (i, t) :: acc) [] tvar_subst in
    match tvar_subst with
    | [] -> b
    | _ -> map_types_in_ast (subst_tvars_type tvar_subst) b

(* Resolve unresolved metas in an ML AST by walking its sub-types.
   resolve_metas should be a function that resolves metas in a single ml_type. *)
let rec resolve_metas_in_ast resolve_metas = function
  | MLlam (_, ty, body) -> resolve_metas ty; resolve_metas_in_ast resolve_metas body
  | MLletin (_, ty, a, b) -> resolve_metas ty; resolve_metas_in_ast resolve_metas a; resolve_metas_in_ast resolve_metas b
  | MLglob (_, tys) -> List.iter resolve_metas tys
  | MLcons (ty, _, args) -> resolve_metas ty; List.iter (resolve_metas_in_ast resolve_metas) args
  | MLcase (ty, e, brs) ->
      resolve_metas ty; resolve_metas_in_ast resolve_metas e;
      Array.iter (fun (ids, ty, _, body) ->
        List.iter (fun (_, t) -> resolve_metas t) ids;
        resolve_metas ty; resolve_metas_in_ast resolve_metas body) brs
  | MLfix (_, ids, funs, _) ->
      Array.iter (fun (_, ty) -> resolve_metas ty) ids;
      Array.iter (resolve_metas_in_ast resolve_metas) funs
  | MLapp (f, args) -> resolve_metas_in_ast resolve_metas f; List.iter (resolve_metas_in_ast resolve_metas) args
  | MLmagic a -> resolve_metas_in_ast resolve_metas a
  | MLparray (arr, def) -> Array.iter (resolve_metas_in_ast resolve_metas) arr; resolve_metas_in_ast resolve_metas def
  | MLtuple args -> List.iter (resolve_metas_in_ast resolve_metas) args
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()

(* Substitute a CPPvar with a replacement expression in C++ ASTs.
   Used when lifting inner functions to top-level to rewrite references. *)
let rec local_var_subst_expr (target : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  let sub = local_var_subst_expr target repl in
  match e with
  | CPPvar id when Id.equal id target -> repl
  | CPPfun_call (f, args) -> CPPfun_call (sub f, List.map sub args)
  | CPPderef e' -> CPPderef (sub e')
  | CPPmove e' -> CPPmove (sub e')
  | CPPlambda (args, ty, b, cbv) -> CPPlambda (args, ty, List.map (local_var_subst_stmt target repl) b, cbv)
  | CPPoverloaded cases -> CPPoverloaded (List.map sub cases)
  | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map sub args)
  | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map sub args)
  | CPPget (e', id') -> CPPget (sub e', id')
  | CPPget' (e', id') -> CPPget' (sub e', id')
  | CPPnamespace (id', e') -> CPPnamespace (id', sub e')
  | CPPparray (args, e') -> CPPparray (Array.map sub args, sub e')
  | CPPmethod_call (obj, meth, args) -> CPPmethod_call (sub obj, meth, List.map sub args)
  | CPPmember (e', mid) -> CPPmember (sub e', mid)
  | CPParrow (e', mid) -> CPParrow (sub e', mid)
  | CPPforward (ty, e') -> CPPforward (ty, sub e')
  | CPPnew (ty, args) -> CPPnew (ty, List.map sub args)
  | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ty, sub e')
  | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, tys, List.map sub args)
  | CPPqualified (e', qid) -> CPPqualified (sub e', qid)
  | CPPbinop (op, lhs, rhs) -> CPPbinop (op, sub lhs, sub rhs)
  | _ -> e
and local_var_subst_stmt (target : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  let sub_e = local_var_subst_expr target repl in
  let sub_s = local_var_subst_stmt target repl in
  match s with
  | Sreturn (Some e) -> Sreturn (Some (sub_e e))
  | Sreturn None -> Sreturn None
  | Sasgn (id, ty, e) -> Sasgn (id, ty, sub_e e)
  | Sexpr e -> Sexpr (sub_e e)
  | Scustom_case (ty, e, tys, brs, str) ->
      Scustom_case (ty, sub_e e, tys,
        List.map (fun (args, ty, stmts) ->
          (args, ty, List.map sub_s stmts)) brs, str)
  | Sif (cond, then_stmts, else_stmts) ->
      Sif (sub_e cond, List.map sub_s then_stmts, List.map sub_s else_stmts)
  | Sassign_field (obj, field, e) ->
      Sassign_field (sub_e obj, field, sub_e e)
  | Sswitch (scrut, ind, brs) ->
      Sswitch (sub_e scrut, ind,
        List.map (fun (ctor, stmts) -> (ctor, List.map sub_s stmts)) brs)
  | _ -> s

(* Build extended tvar names covering both signature and body Tvar indices.
   sig_indices: sorted list of Tvar indices from the function signature
   sig_names: corresponding Id.t names for those indices
   body_tvars: sorted-unique list of all Tvar indices found in the body *)
let build_extended_tvar_names sig_indices sig_names body_tvars =
  let n_sig = List.length sig_indices in
  let sig_set = IntSet.of_list sig_indices in
  let body_extra_tvars = List.filter (fun i -> not (IntSet.mem i sig_set)) body_tvars in
  let max_tvar = List.fold_left max 0 (sig_indices @ body_tvars) in
  let tvar_name_map = List.map2 (fun i name -> (i, name)) sig_indices sig_names in
  let tvar_name_map =
    if body_extra_tvars <> [] then begin
      let min_sig = List.hd sig_indices in
      let min_extra = List.fold_left min max_int body_extra_tvars in
      let offset = min_extra - min_sig in
      List.fold_left (fun acc i ->
        let mapped_sig_idx = i - offset in
        if mapped_sig_idx >= 1 && mapped_sig_idx <= n_sig then
          let name = List.assoc mapped_sig_idx tvar_name_map in
          (i, name) :: acc
        else
          (i, Id.of_string ("T" ^ string_of_int i)) :: acc
      ) tvar_name_map body_extra_tvars
    end else tvar_name_map
  in
  if max_tvar > 0 then
    List.init max_tvar (fun i ->
      let idx = i + 1 in
      match List.assoc_opt idx tvar_name_map with
      | Some name -> name
      | None -> Id.of_string ("_tvar" ^ string_of_int idx))
  else sig_names

(* Convert ML params to C++ types with const/ref wrapping, and create forwarding-ref
   template parameters for function-typed params.
   convert_fn: function to convert ml_type -> cpp_type (typically convert_ml_type_to_cpp_type env Refset'.empty tvar_names)
   Returns (cpp_params, all_temps_with_funs). *)
let build_lifted_cpp_params convert_fn base_temps params =
  let cpp_params = List.map (fun (id, ty) ->
    let cpp_ty = convert_fn ty in
    match cpp_ty with
    | Tshared_ptr _ -> (id, Tref (Tmod (TMconst, cpp_ty)))
    | _ -> (id, Tmod (TMconst, cpp_ty))) params in
  let fun_tys = List.filter_map (fun (x, ty, j) ->
      match ty with
      | Tmod (TMconst, Tfun (dom, cod_f)) ->
          Some (x, TTfun (dom, cod_f), Id.of_string ("F" ^ (string_of_int j)))
      | _ -> None) (List.mapi (fun j (x, ty) -> (x, ty, j)) (List.rev cpp_params)) in
  let n_params = List.length cpp_params in
  let cpp_params = List.mapi (fun j (x, ty) ->
      match ty with
      | Tmod (TMconst, Tfun (_, _)) ->
        (x, Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ (string_of_int (n_params - j - 1))))))))
      | _ -> (x, ty)) cpp_params in
  let extra_temps = List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let all_temps_with_funs = base_temps @ extra_temps in
  (cpp_params, all_temps_with_funs)

(* Extract return type from a function type, stripping all Tarr layers. *)
let rec ml_return_type = function
  | Tarr (_, rest) -> ml_return_type rest
  | t -> t

(* Extract argument types and return type from a function type. *)
let rec get_args_and_ret acc = function
  | Tarr (t, rest) -> get_args_and_ret (t :: acc) rest
  | ret_ty -> (List.rev acc, ret_ty)

(* Check if a GlobRef returns a typeclass type (possibly through Tarr layers). *)
let ref_returns_typeclass r =
  try Table.is_typeclass_type (ml_return_type (Table.find_type r))
  with Not_found -> false

(* Use Common.extract_at_pos for extracting elements at a position *)

(* Create a substitution function for extra type variables in C++ types.
   num_ind_vars: number of type vars from the containing inductive/record
   extra_tvar_map: mapping from Tvar index to Id for extra type vars *)
let make_subst_extra_tvars num_ind_vars extra_tvar_map =
  let rec subst = function
    | Tvar (i, None) when List.mem_assoc i extra_tvar_map ->
        Tvar (0, Some (List.assoc i extra_tvar_map))
    | Tvar (i, None) when i >= 1 && i <= num_ind_vars ->
        (* Inductive's type var - keep as-is for tvar_subst_stmt *)
        Tvar (i, None)
    | Tfun (dom, cod) -> Tfun (List.map subst dom, subst cod)
    | Tshared_ptr t -> Tshared_ptr (subst t)
    | Tunique_ptr t -> Tunique_ptr (subst t)
    | Tglob (r, args, e) -> Tglob (r, List.map subst args, e)
    | Tref t -> Tref (subst t)
    | Tmod (m, t) -> Tmod (m, subst t)
    | Tvariant tys -> Tvariant (List.map subst tys)
    | Tnamespace (r, t) -> Tnamespace (r, subst t)
    | Tqualified (t, id) -> Tqualified (subst t, id)
    | t -> t
  in
  subst


(* Replace all unnamed Tvars with Tany (for type erasure in indexed inductives).
   Used when a type has Tvars that don't correspond to any template parameters.
   This is defined early so it can be used in gen_cpp_pat_lambda and gen_ind_header_v2. *)
let rec tvar_erase_type (ty : cpp_type) : cpp_type =
  match ty with
  | Tvar (_, None) -> Tany
  | Tvar (_, Some _) -> ty  (* Named Tvars are kept *)
  | Tglob (r, tys, args) -> Tglob (r, List.map tvar_erase_type tys, args)
  | Tfun (tys, ty) -> Tfun (List.map tvar_erase_type tys, tvar_erase_type ty)
  | Tmod (m, ty) -> Tmod (m, tvar_erase_type ty)
  | Tnamespace (r, ty) -> Tnamespace (r, tvar_erase_type ty)
  | Tref ty -> Tref (tvar_erase_type ty)
  | Tvariant tys -> Tvariant (List.map tvar_erase_type tys)
  | Tshared_ptr ty -> Tshared_ptr (tvar_erase_type ty)
  | Tunique_ptr ty -> Tunique_ptr (tvar_erase_type ty)
  | Tid (id, tys) -> Tid (id, List.map tvar_erase_type tys)
  | Tqualified (ty, id) -> Tqualified (tvar_erase_type ty, id)
  | _ -> ty  (* Tvoid, Ttodo, Tunknown, Tany *)

(* Check if a C++ type contains any unnamed Tvar (Tvar(_, None)).
   Used to detect types that can't be fully resolved in monomorphized contexts
   (tvars=[]), where nested Tvar(_, None) would print as invalid C++ like List<T1>. *)
let rec has_unnamed_tvar (ty : cpp_type) : bool =
  match ty with
  | Tvar (_, None) -> true
  | Tvar (_, Some _) -> false
  | Tglob (_, tys, _) -> List.exists has_unnamed_tvar tys
  | Tfun (tys, ty) -> List.exists has_unnamed_tvar tys || has_unnamed_tvar ty
  | Tmod (_, ty) -> has_unnamed_tvar ty
  | Tnamespace (_, ty) -> has_unnamed_tvar ty
  | Tref ty -> has_unnamed_tvar ty
  | Tvariant tys -> List.exists has_unnamed_tvar tys
  | Tshared_ptr ty -> has_unnamed_tvar ty
  | Tunique_ptr ty -> has_unnamed_tvar ty
  | Tid (_, tys) -> List.exists has_unnamed_tvar tys
  | Tqualified (ty, _) -> has_unnamed_tvar ty
  | _ -> false

(* Check if a C++ type is Tany or contains an unnamed Tvar (which becomes Tany).
   This is used to identify methods that return std::any due to type erasure in indexed inductives. *)
let rec type_is_erased (ty : cpp_type) : bool =
  match ty with
  | Tany -> true
  | Tvar (_, None) -> true  (* Will become Tany after tvar_erase_type *)
  | Tvar (_, Some _) -> false  (* Named Tvar - not erased *)
  | Tglob (_, _, _) -> false
  | Tfun (_, _) -> false  (* Functions aren't erased *)
  | Tmod (_, inner) -> type_is_erased inner
  | Tnamespace (_, inner) -> type_is_erased inner
  | _ -> false

(* Collect de Bruijn indices of free variables in an ML AST.
   n_bound is the number of locally bound variables (lambda params, let bindings, etc.).
   Returns indices relative to the outer scope (i.e., i - n_bound for each free MLrel i). *)
let rec collect_free_rels_set n_bound acc = function
  | MLrel i -> if i > n_bound then IntSet.add (i - n_bound) acc else acc
  | MLlam (_, _, body) -> collect_free_rels_set (n_bound + 1) acc body
  | MLletin (_, _, a, b) ->
      collect_free_rels_set n_bound (collect_free_rels_set (n_bound + 1) acc b) a
  | MLapp (f, args) ->
      List.fold_left (collect_free_rels_set n_bound) (collect_free_rels_set n_bound acc f) args
  | MLcase (_, e, brs) ->
      let acc = collect_free_rels_set n_bound acc e in
      Array.fold_left (fun acc (ids, _, _, body) ->
        collect_free_rels_set (n_bound + List.length ids) acc body) acc brs
  | MLfix (_, ids, funs, _) ->
      let n_fix = Array.length ids in
      Array.fold_left (fun acc f ->
        let params, body = collect_lams f in
        collect_free_rels_set (n_bound + List.length params + n_fix) acc body) acc funs
  | MLcons (_, _, args) -> List.fold_left (collect_free_rels_set n_bound) acc args
  | MLmagic a -> collect_free_rels_set n_bound acc a
  | MLtuple args -> List.fold_left (collect_free_rels_set n_bound) acc args
  | MLparray (arr, def) ->
      collect_free_rels_set n_bound (Array.fold_left (collect_free_rels_set n_bound) acc arr) def
  | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> acc

let collect_free_rels n_bound body =
  IntSet.elements (collect_free_rels_set n_bound IntSet.empty body)

let rec convert_ml_type_to_cpp_type env (ns : Refset'.t) (tvars : Id.t list) (ml_t : ml_type) : cpp_type =
  match ml_t with
  | Tarr (t1, t2) ->
        let t1c = convert_ml_type_to_cpp_type env ns tvars t1 in
        let t2c = convert_ml_type_to_cpp_type env ns tvars t2 in
        (* Skip erased params: isTdummy catches direct Tdummy, is_cpp_dummy_type
           catches Tdummy wrapped in Tmeta (e.g., Tmeta{contents=Some(Tdummy Kprop)}
           which converts to dummy_prop glob).  Do NOT use is_erased_type here as
           it also catches Tany (std::any), which is a valid type for universally
           quantified parameters — stripping it would incorrectly collapse
           (A -> IO) into just IO. *)
        if isTdummy t1 || is_cpp_dummy_type t1c then t2c else
        (match t2c with
        | Tfun (l, t) -> Tfun (t1c::l, t)
        | _ -> Tfun (t1c::[], t2c))
  | Tglob (g, _, _) when is_void g -> Tvoid
  (* Erased carrier projections from promoted dependent records:
     Convert Tglob(m_carrier, []) to Tvar with the promoted var name. *)
  | Tglob (g, ts, _) when Table.is_promoted_type_var g ->
      (match Table.promoted_type_var_name g with
       | Some var_id -> Tvar (1000, Some var_id)
       | None -> Tany)
  | Tglob (g, ts, args) when is_custom g ->
    Tglob (g, List.map (convert_ml_type_to_cpp_type env ns tvars) ts, List.map (gen_expr env) args)
  | Tglob (g, ts, _) ->
      (* For inductives, only keep type args that correspond to parameters (not indices).
         Parameters become template params in C++; indices are erased. *)
      let filtered_ts = match g with
        | GlobRef.IndRef (kn, _) ->
            (* Filter type args to keep only parameters (not indices).
               Use get_ind_num_param_vars_opt to determine how many to keep.
               For local/self-references with non-empty tvars, we can use tvars length
               as a fallback, but prefer the table lookup for accuracy. *)
            (match Table.get_ind_num_param_vars_opt kn with
            | Some num_param_vars ->
                (* Only keep the first num_param_vars type args - the rest are indices *)
                List.firstn num_param_vars ts
            | None ->
                (* Fallback: if tvars is non-empty and this is a local reference, use tvars length *)
                let is_local = Refset'.mem g ns ||
                               List.exists (Environ.QGlobRef.equal Environ.empty_env g) !local_inductives in
                if is_local && tvars <> [] then
                  List.firstn (List.length tvars) ts
                else
                  ts)  (* Keep all if we can't determine *)
        | _ -> ts
      in
      let converted_ts = List.map (convert_ml_type_to_cpp_type env ns tvars) filtered_ts in
      let core = Tglob (g, converted_ts, []) in
      (match g with
      | GlobRef.IndRef _ ->
        (* Enum inductives are value types - no shared_ptr wrapping *)
        if is_enum_inductive g then
          let is_local = Refset'.mem g ns ||
                         List.exists (Environ.QGlobRef.equal Environ.empty_env g) !local_inductives in
          if is_local then core
          else Tnamespace (g, core)
        else
        (* Check if this inductive is in the explicit ns list or in local_inductives context *)
        let is_local = Refset'.mem g ns ||
                       List.exists (Environ.QGlobRef.equal Environ.empty_env g) !local_inductives in
        if is_local then Tshared_ptr core
        else if not (get_record_fields g == []) then Tshared_ptr core
        else Tshared_ptr (Tnamespace (g, core))
      | _ -> core)
  | Tvar i | Tvar' i ->
      (try Tvar (i, Some (List.nth tvars (pred i)))
       with Failure _ -> Tvar (i, None))
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ns tvars t
  | Tmeta {id = i} ->
      (* Unresolved meta - use std::any for type erasure.
         This happens for existential type variables in indexed inductives. *)
      Tany
  (* Tdummy marks erased type/prop/implicit parameters in the ML AST.
     We convert them to Tglob(VarRef "dummy_*") as intermediate markers so that
     downstream filtering (is_cpp_dummy_type / is_erased_type / filter_erased_type_args
     in gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them.  These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Tdummy Ktype -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_type")), [], [])
  | Tdummy Kprop -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_prop")), [], [])
  | Tdummy (Kimplicit _) -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_implicit")), [], [])
  | Tstring -> assert false (* Tstring is not used by the extraction pipeline *)
  | Tunknown -> Tany
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string ("axiom")), [], [])
  (*
      let _ = print_endline "TODO: TMETA OR TDUMMY OR TUNKNOWN OR TAXIOM"  in
      assert false *)

(* Generate code for a custom-extracted constructor application *)
and gen_expr_custom_cons env (ty : ml_type) r ts =
  let args = List.rev_map (gen_expr env) ts in
  let app x = (match args with
    | [] -> x
    | _ -> CPPfun_call(x, args)) in
  (match ty with
  | Miniml.Tglob (n, tys, _) ->
    (* Filter out index type args - only keep parameters *)
    let tys = match n with
      | GlobRef.IndRef (kn, _) ->
          (match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars -> List.firstn num_param_vars tys
          | None -> tys)
      | _ -> tys
    in
    let temps = List.map (convert_ml_type_to_cpp_type env Refset'.empty []) tys in
    app (mk_cppglob r temps)
  | _ -> app (mk_cppglob r []))

(* Try to fold a Peano numeral chain (nested constructors) into an integer *)
and try_fold_numeral info expr =
  match expr with
  | MLcons (_ty, cr, []) ->
    (match cr with
     | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_zero_ctor -> Some 0
     | _ -> None)
  | MLcons (_ty, cr, [inner]) ->
    (match cr with
     | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_succ_ctor ->
       Option.map (fun n -> n + 1) (try_fold_numeral info inner)
     | _ -> None)
  | MLmagic inner -> try_fold_numeral info inner
  | _ -> None

(* TODO: when an MLGlob has monadic type, needs to be funcall *)
and gen_expr env (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i ->
    let var_expr = (try CPPvar (get_db_name i env) with Failure _ -> CPPvar (Id.of_string ("_db" ^ string_of_int i))) in
    (* Phase 2: move on last use.
       Emit std::move if: (1) the variable is dead after this point,
       (2) it's an owned variable (not borrowed), and
       (3) this is its only occurrence in the current RHS expression. *)
    if Escape.IntSet.mem i tctx.move_dead_after
       && Escape.IntSet.mem i tctx.move_owned_vars then
      CPPmove var_expr
    else
      var_expr
  | MLapp (MLmagic t, args) -> gen_expr env (MLapp (t, args))
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    let t = Common.last (a1 :: l) in
    gen_expr env t
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
    gen_expr env (MLapp (a1, a2::[])) *)
  | MLapp (MLfix _, _) as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles MLapp(MLfix ...). *)
    with_escape_analysis a (fun () ->
      CPPfun_call (CPPlambda([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false), []))
  | MLapp (MLapp (MLglob _ as g, inner_args), outer_args) ->
    (* Flatten nested MLapp when inner callee is a global reference.
       This arises from Rocq partial applications like:
         div_conq_split x f1 f2 l
       which extracts as MLapp(MLapp(MLglob(dcs), [x,f1,f2]), [l]).
       Flattening to MLapp(MLglob(dcs), [x,f1,f2,l]) lets eta_fun see
       the complete argument list and generate a direct call. *)
    eta_fun env g (inner_args @ outer_args)
  | MLapp (f, args) ->
    eta_fun env f args
  | MLlam _ as a ->
      let args,a = collect_lams a in
      let lam_params = List.map (fun (x, y) -> (id_of_mlid x, y)) args in
      let args,env = push_vars' lam_params env in
      let saved_env_types = tctx.env_types in
      push_env_types args;
      let filtered_args = List.filter (fun (_,ty) -> not (isTdummy ty)) args in
      let f = with_escape_analysis a (fun () ->
        let tvars = get_current_type_vars () in
        let cpp_args = List.map (fun (id, ty) -> (convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id)) filtered_args in
        (* Generate the body, then check if the body returns a lambda
           (this happens when extract_cons_app generates curried partial
           constructor applications with an MLmagic barrier).  If so,
           convert the returned lambda to capture by value to avoid
           dangling references to the outer lambda's parameters. *)
        let body_stmts = gen_stmts env (fun x -> Sreturn (Some x)) a in
        let body_stmts = List.map (fun s -> match s with
          | Sreturn (Some (CPPlambda (args, ret, body, false))) ->
              Sreturn (Some (CPPlambda (args, ret, body, true)))
          | s -> s) body_stmts in
        CPPlambda (cpp_args, None, body_stmts, false)) in
      tctx.env_types <- saved_env_types;
      (match filtered_args with
      | [] ->
        (* All lambda params are dummy (type abstractions).  Skip the lambda
           wrapper and generate the body expression directly.  However, when
           the body is a reference to a template function (detectable by
           having Tdummy-typed leading params in its ML type), we must wrap
           it in a generic forwarding lambda — C++ cannot pass overloaded or
           template function names as first-class values. *)
        (match a with
        | MLglob (r, tys_inner) ->
          let ml_ty = try Table.find_type r with Not_found -> Tunknown in
          let has_dummy_prefix = function
            | Tarr (t, _) when isTdummy t -> true
            | _ -> false in
          if has_dummy_prefix ml_ty then
            (* The function is a template that had type-level leading params.
               We need a forwarding lambda because C++ can't pass template
               function names as first-class values.

               To handle non-deducible template type params (like T2 that only
               appears in the return type), we use a C++20 template lambda with
               explicitly typed value parameters.  This lets the compiler deduce
               type variables from the argument types, and we compute non-deducible
               tvars via std::invoke_result_t. *)
            let rec collect_non_dummy_types = function
              | Miniml.Tarr (t, rest) when not (isTdummy t) -> t :: collect_non_dummy_types rest
              | Miniml.Tarr (_, rest) -> collect_non_dummy_types rest
              | _ -> [] in
            let non_dummy_param_tys = collect_non_dummy_types ml_ty in
            let n = List.length non_dummy_param_tys in
            let arg_names = List.init n (fun i -> "_a" ^ string_of_int i) in
            let fn_name = Common.pp_global_name Term r in
            (* Collect all tvars from the ML type *)
            let all_tvars_set = List.fold_left collect_tvars_set IntSet.empty (non_dummy_param_tys @ [ml_ty]) in
            let all_tvars = IntSet.elements all_tvars_set in
            (* Tvars deducible from non-function value params *)
            let value_param_tys = List.filter (fun t -> match t with Miniml.Tarr _ -> false | _ -> true) non_dummy_param_tys in
            let deducible_set = List.fold_left collect_tvars_set IntSet.empty value_param_tys in
            let deducible_tvars = IntSet.elements deducible_set in
            let non_deducible_tvars = List.filter (fun i -> not (IntSet.mem i deducible_set)) all_tvars in
            (* Create tvar names for the template lambda *)
            let tvar_name i = "_T" ^ string_of_int i in
            (* Render an ML type as a C++ type string using local tvar names *)
            let rec render_ml_ty = function
              | Miniml.Tvar i | Miniml.Tvar' i -> tvar_name i
              | Miniml.Tarr (t1, t2) -> "std::function<" ^ render_ml_ty t2 ^ "(" ^ render_ml_ty t1 ^ ")>"
              | Miniml.Tglob (g, ts, _) when is_custom g ->
                (* Custom types may use %t0, %t1 placeholders for type args *)
                let custom_str = find_custom g in
                let rendered_ts = List.map render_ml_ty ts in
                let len = String.length custom_str in
                let buf = Buffer.create len in
                let rec subst i =
                  if i >= len then ()
                  else if i <= len - 3 && custom_str.[i] = '%' && custom_str.[i+1] = 't'
                       && custom_str.[i+2] >= '0' && custom_str.[i+2] <= '9' then begin
                    let digit_start = i + 2 in
                    let rec find_end j =
                      if j < len && custom_str.[j] >= '0' && custom_str.[j] <= '9'
                      then find_end (j + 1) else j in
                    let digit_end = find_end digit_start in
                    let idx = int_of_string (String.sub custom_str digit_start (digit_end - digit_start)) in
                    if idx < List.length rendered_ts then
                      Buffer.add_string buf (List.nth rendered_ts idx)
                    else
                      Buffer.add_string buf (String.sub custom_str i (digit_end - i));
                    subst digit_end
                  end else begin
                    Buffer.add_char buf custom_str.[i];
                    subst (i + 1)
                  end
                in
                subst 0;
                Buffer.contents buf
              | Miniml.Tglob (g, ts, _) ->
                let is_ind = match g with GlobRef.IndRef _ -> true | _ -> false in
                let base = Common.pp_global_name (if is_ind then Type else Term) g in
                let type_str = if ts = [] then base
                  else base ^ "<" ^ String.concat ", " (List.map render_ml_ty ts) ^ ">" in
                if is_ind && not (Table.is_enum_inductive g) then
                  "std::shared_ptr<" ^ type_str ^ ">"
                else type_str
              | Miniml.Tdummy _ -> "std::any"
              | _ -> "auto" in
            if non_deducible_tvars <> [] && not (IntSet.is_empty deducible_set) then
              (* There are non-deducible tvars — use template lambda with typed params.
                 The first param (function type) uses auto&&, value params get specific types. *)
              let template_params = String.concat ", " (List.map (fun i ->
                "typename " ^ tvar_name i) deducible_tvars) in
              let params = List.mapi (fun i ty ->
                match ty with
                | Miniml.Tarr _ ->
                  (* Function-typed param: use auto&& *)
                  "auto &&" ^ List.nth arg_names i
                | _ ->
                  (* Value param: use specific type for tvar deduction *)
                  "const " ^ render_ml_ty ty ^ " &" ^ List.nth arg_names i
              ) non_dummy_param_tys in
              let params_str = String.concat ", " params in
              let fwd_args = String.concat ", " (List.mapi (fun i ty ->
                match ty with
                | Miniml.Tarr _ -> "std::forward<decltype(" ^ List.nth arg_names i ^ ")>(" ^ List.nth arg_names i ^ ")"
                | _ -> List.nth arg_names i
              ) non_dummy_param_tys) in
              (* Build explicit type args: deducible tvars + non-deducible computed via invoke_result_t *)
              let deducible_args = List.map tvar_name deducible_tvars in
              let non_deducible_args = List.map (fun _i ->
                (* Compute as invoke_result_t<F&, deducible_tvars&...> where F is the first function param *)
                let f_param = List.nth arg_names 0 in
                let deducible_refs = String.concat ", " (List.map (fun j ->
                  tvar_name j ^ " &") deducible_tvars) in
                "std::invoke_result_t<decltype(" ^ f_param ^ ") &, " ^ deducible_refs ^ ">"
              ) non_deducible_tvars in
              let all_type_args = deducible_args @ non_deducible_args in
              let ty_args_str = "<" ^ String.concat ", " all_type_args ^ ">" in
              CPPraw ("[]<" ^ template_params ^ ">(" ^ params_str ^ ") -> decltype(auto) { return " ^
                      fn_name ^ ty_args_str ^ "(" ^ fwd_args ^ "); }")
            else
              (* No non-deducible tvars or no deducible tvars — simple forwarding *)
              let params_str = String.concat ", " (List.map (fun s -> "auto &&" ^ s) arg_names) in
              let fwd_args = String.concat ", " (List.map (fun s ->
                "std::forward<decltype(" ^ s ^ ")>(" ^ s ^ ")") arg_names) in
              (* Convert inner type args to C++ types, filtering out Tany *)
              let inner_tvars = get_current_type_vars () in
              let tys_cpp = List.map (convert_ml_type_to_cpp_type env Refset'.empty inner_tvars) tys_inner in
              let tys_cpp = List.filter (fun t -> t <> Tany) tys_cpp in
              let ty_args_str = match tys_cpp with
                | [] -> ""
                | _ ->
                  let rec render_ty = function
                    | Tvar (_, Some n) -> Id.to_string n
                    | Tvar (i, None) -> "T" ^ string_of_int i
                    | Tglob (r, [], _) -> Common.pp_global_name Type r
                    | Tglob (r, tys, _) ->
                      Common.pp_global_name Type r ^ "<" ^
                      String.concat ", " (List.map render_ty tys) ^ ">"
                    | Tshared_ptr ty -> "std::shared_ptr<" ^ render_ty ty ^ ">"
                    | Tunique_ptr ty -> "std::unique_ptr<" ^ render_ty ty ^ ">"
                    | _ -> "auto" in
                  "<" ^ String.concat ", " (List.map render_ty tys_cpp) ^ ">" in
              CPPraw ("[](" ^ params_str ^ ") -> decltype(auto) { return " ^
                      fn_name ^ ty_args_str ^ "(" ^ fwd_args ^ "); }")
          else
            gen_expr env a
        | _ ->
            (* Body is not a template function ref — wrap in void thunk (old behavior).
               gen_expr env a might produce lambdas with [&] capture which fail at
               static scope, so we use the pre-built capture-free lambda f. *)
            CPPfun_call (f, []))
      | _ -> f)
  | MLglob (x, tys) when is_inline_custom x ->
      let tvars = get_current_type_vars () in
      let ty = find_type x in
      let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ty in
      (match ty with
      | Tfun (dom, cod) -> eta_fun env (MLglob (x, tys)) [] (* TODO: could be only if contains '%' *)
      | _ -> mk_cppglob x (List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys))
  | MLglob (x, tys) ->
      let tvars = get_current_type_vars () in
      let tys_cpp = List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys in
      (* If any type arg is Tany or a dummy type glob (from erased type/prop params),
         drop ALL explicit type args via filter_erased_type_args and let the
         compiler deduce everything.  See filter_erased_type_args for why we
         must drop all args rather than just the erased ones. *)
      mk_cppglob x (filter_erased_type_args tys_cpp)
  | MLcons (_ty, r, _ts) when (match r with
      | GlobRef.ConstructRef ((kn, i), _) -> Table.is_numeral_inductive (GlobRef.IndRef (kn, i))
      | _ -> false) ->
    (* Try to fold Peano numeral chain into an integer literal *)
    let ind_ref = match r with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ -> assert false
    in
    (match Table.get_numeral_info ind_ref with
     | Some info ->
       (match try_fold_numeral info ml_e with
        | Some n ->
          let rendered = Str.global_replace (Str.regexp_string "%n")
                           (string_of_int n) info.Table.num_fmt in
          CPPraw rendered
        | None ->
          (* Not a complete literal; fall through to normal custom handling *)
          gen_expr_custom_cons env _ty r _ts)
     | None -> gen_expr_custom_cons env _ty r _ts)
  | MLcons (ty, r, ts) when is_custom r ->
    gen_expr_custom_cons env ty r ts
  | MLcons (ty, r, ts) when ts = [] && (match r with GlobRef.ConstructRef ((kn, _), _) -> is_enum_inductive (GlobRef.IndRef (kn, 0)) | _ -> false) ->
    (* Enum constructor: emit bare EnumType::Constructor value *)
    let ctor_name = Id.of_string (Common.pp_global_name Type r) in
    let ind_ref = (match r with GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i) | _ -> assert false) in
    CPPenum_val (ind_ref, ctor_name)
  | MLcons (ty, r, ts) ->
    let fds = record_fields_of_type ty in
    (match fds with
      | [] ->
      (* Propagate resolved types to nested list constructors before code generation.
         For List<nat> constructors like cons(1, cons(2, nil)), this ensures the
         nested nil gets List<nat> type instead of List<std::any>. *)
      let ts_updated = (match ty with
        | Tglob (n, tys_orig, schema_opt) ->
          (* Only run type propagation for list constructors *)
          let is_list = (try String.equal (Common.pp_global_name Type n) "list" with _ -> false) in
          if not is_list then ts
          else
          (* Filter out index type args - only keep parameters *)
          let tys_filt = match n with
            | GlobRef.IndRef (kn, _) ->
                (match Table.get_ind_num_param_vars_opt kn with
                | Some num_param_vars -> List.firstn num_param_vars tys_orig
                | None -> tys_orig)
            | _ -> tys_orig
          in
          (* Resolve Tunknown from element types *)
          let has_unknown = List.exists (fun (t : ml_type) -> match t with Tunknown -> true | _ -> false) tys_filt in
          if has_unknown && (match ts with [] -> false | _ -> true) then
            let tys_resolved = List.map (fun (t : ml_type) -> match t with
              | Tunknown ->
                let first_elem = List.find_opt (fun a -> match a with MLdummy _ -> false | _ -> true) ts in
                (match first_elem with
                 | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
                 | Some (MLcons (elem_ty, _, _)) -> elem_ty
                 | _ -> t)
              | _ -> t) tys_filt in
            (* Propagate resolved type to nested constructors *)
            let resolved_ty = Miniml.Tglob (n, tys_resolved, schema_opt) in
            let rec update_nested_ty ast =
              match ast with
              | MLcons (arg_typ, arg_c, arg_ts) ->
                (match arg_typ with
                 | Miniml.Tglob (arg_ref, arg_tys, _) when GlobRef.CanOrd.equal arg_ref n &&
                                                            List.exists (fun t -> match t with Miniml.Tunknown -> true | _ -> false) arg_tys ->
                   MLcons (resolved_ty, arg_c, List.map update_nested_ty arg_ts)
                 | _ ->
                   MLcons (arg_typ, arg_c, List.map update_nested_ty arg_ts))
              | MLmagic inner ->
                MLmagic (update_nested_ty inner)
              | other -> other
            in
            List.map update_nested_ty ts
          else ts
        | _ -> ts) in
      (* Generate: Type<temps>::ctor::Constructor_(args) *)
      let gen_ctor_call args = (match ty with
      | Tglob (n, tys, _) ->
        (* Filter out index type args - only keep parameters *)
        let tys = match n with
          | GlobRef.IndRef (kn, _) ->
              (match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> List.firstn num_param_vars tys
              | None -> tys)
          | _ -> tys
        in
        (* Resolve Tunknown type args from constructor element types.
           For cons(elem, rest), elem's type provides the list's type param. *)
        let has_unknown = List.exists (fun (t : ml_type) -> match t with Tunknown -> true | _ -> false) tys in
        let tys = if has_unknown && (match ts_updated with [] -> false | _ -> true) then
          List.map (fun (t : ml_type) -> match t with
            | Tunknown ->
              (* Infer from first non-MLmagic/MLdummy constructor arg *)
              let first_elem = List.find_opt (fun a -> match a with MLdummy _ -> false | _ -> true) ts_updated in
              (match first_elem with
               | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
               | Some (MLcons (elem_ty, _, _)) -> elem_ty
               | _ -> t)
            | _ -> t) tys
        else tys in
        let tvars = get_current_type_vars () in
        let temps = List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys in
        (* Get the constructor base name (without module path) and add underscore suffix *)
        let ctor_name = Common.pp_global_name Type r in
        let factory_name = Id.of_string (ctor_name ^ "_") in
        (* Build: Type<temps>::ctor::Factory_(args) *)
        let type_expr = mk_cppglob n temps in
        let ctor_expr = CPPqualified (type_expr, Id.of_string "ctor") in
        let factory_expr = CPPqualified (ctor_expr, factory_name) in
        CPPfun_call (factory_expr, args)
      | _ ->
        (* Fallback for non-Tglob types - shouldn't happen in practice *)
        let ctor_name = Common.pp_global_name Type r in
        let factory_name = Id.of_string (ctor_name ^ "_") in
        let ctor_expr = CPPqualified (mk_cppglob r [], Id.of_string "ctor") in
        let factory_expr = CPPqualified (ctor_expr, factory_name) in
        CPPfun_call (factory_expr, args)) in
      (* Note: CPPfun_call reverses args when printing, so we reverse here.
         For MLdummy constructor args (erased prop/type values), generate std::any{}
         instead of the default CPPabort throw expression, since the corresponding
         parameter type is std::any and throw has type void. *)
      let gen_ctor_arg e = match e with
        | MLdummy _ -> CPPraw "std::any{}"
        | _ -> gen_expr env e
      in
      gen_ctor_call (List.rev_map gen_ctor_arg ts_updated)
    | _ ->
      (* Records - keep using make_shared pattern for now *)
      let nstempmod args = (match ty with
      | Tglob (n, tys, _) ->
        (* Filter out index type args - only keep parameters *)
        let tys = match n with
          | GlobRef.IndRef (kn, _) ->
              (match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> List.firstn num_param_vars tys
              | None -> tys)
          | _ -> tys
        in
        let temps = List.map (convert_ml_type_to_cpp_type env Refset'.empty []) tys in
        CPPfun_call (CPPmk_shared (Tglob (n, temps, [])), [CPPstruct (n, temps, args)])
      | _ -> assert false) in
      nstempmod (List.map (gen_expr env) ts))
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let cexp = gen_custom_cpp_case env (fun x -> Sreturn (Some x)) typ t pv in
    CPPfun_call (CPPlambda([], None, [cexp], false), [])
  (* TODO: SLOPPY and incomplete *)
  | MLcase (typ, t, pv) when (not (record_fields_of_type typ == []) && Array.length pv == 1) ->
    let (ids,r,pat,body) = pv.(0) in
    let n = List.length ids in
    let is_typeclass = Table.is_typeclass_type typ in
    (* Build lists that correctly account for erased fields.
       record_fields_of_type includes None entries for erased fields;
       ids only contains non-erased bindings. So MLrel i refers to the i-th
       non-erased field. We filter out None entries for correct indexing. *)
    let all_fields = record_fields_of_type typ in
    let non_erased_fields = List.filter_map Fun.id all_fields in
    let all_field_types = match typ with
      | Tglob (r, _, _) -> Table.record_field_types r
      | _ -> [] in
    let non_erased_field_types = List.filter (fun t -> not (isTdummy t)) all_field_types in
    (* For type classes, use qualified access (::) instead of arrow (->) since
       type class instances are template type parameters, not runtime values *)
    let make_field_access base_expr fld =
      if is_typeclass then
        let fld_name = Id.of_string (Common.pp_global_name Term fld) in
        CPPqualified (base_expr, fld_name)
      else
        CPPget' (base_expr, fld)
    in
    (* Strip MLmagic wrappers from the body — promoted dependent records
       may wrap field references in MLmagic due to Tvar/Tglob mismatches *)
    let body' = match body with MLmagic b -> b | b -> b in
    (match body' with
    | MLrel i when i <= n ->
      let fld = try Some (List.nth non_erased_fields (n - i)) with _ -> None in
      (match fld with
      | Some fld ->
        let access = make_field_access (gen_expr env t) fld in
        if is_typeclass then
          (* For typeclasses, non-function value fields (like m_id : carrier)
             are generated as nullary static methods, so we need () to call them *)
          let fld_ty = try List.nth non_erased_field_types (n - i) with _ -> Miniml.Tunknown in
          let is_value_field = match fld_ty with Miniml.Tarr _ -> false | _ -> true in
          if is_value_field then CPPfun_call (access, [])
          else access
        else access
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | MLapp (MLrel i, args) when i <= n ->
      let fld = try Some (List.nth non_erased_fields (n - i)) with _ -> None in
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (match fld with
      (* CPPfun_call expects args in reverse order; List.rev_map both converts and reverses *)
      | Some fld -> CPPfun_call (make_field_access (gen_expr env t) fld, List.rev_map (gen_expr env') args)
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | MLapp (MLmagic (MLrel i), args) when i <= n ->
      let fld = try Some (List.nth non_erased_fields (n - i)) with _ -> None in
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (match fld with
      | Some fld -> CPPfun_call (make_field_access (gen_expr env t) fld, List.rev_map (gen_expr env') args)
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | _ ->
      (* Destructure record fields into local variables, then evaluate the
         body in an IIFE.  push_vars' may rename variables to avoid shadowing
         identifiers already in scope — e.g. when a record has a field
         [rn_value] and the enclosing struct also has an accessor method
         [rn_value], push_vars' renames the local to [rn_value0].

         We must use the renamed ids from push_vars' for the assignment
         declarations so that they are consistent with env' (which the body
         is generated under).  Otherwise the declarations would use the
         original names while the body references the renamed ones. *)
      let renamed_ids,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (* renamed_ids is in reversed order (from List.rev_map above).
         Reverse it back so it aligns with ids (constructor / field order). *)
      let renamed_ids_fwd = List.rev renamed_ids in
      let asgns = List.mapi (fun i ((renamed_name, _), (_, ty)) ->
        let fld = try Some (List.nth non_erased_fields i) with _ -> None in
        let e = (match fld with
          | Some fld -> make_field_access (gen_expr env t) fld
          | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj")) in
        Sasgn (renamed_name, Some (convert_ml_type_to_cpp_type env Refset'.empty [] ty), e)) (List.combine renamed_ids_fwd ids) in
      CPPfun_call (CPPlambda([], None, asgns @ gen_stmts env' (fun x -> Sreturn (Some x)) body, false), []))
      (* TODO: ugly. should better attempt when generating statements! *)
      (* TODO: we don't currently support the fancy thing of pattern matching on record fields at the same time *)
  | MLcase (typ, t, pv) when lang () == Cpp -> gen_cpp_case typ t env pv
  | MLletin (_, ty, _, _) as a ->
      with_escape_analysis a (fun () ->
        CPPfun_call (CPPlambda([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false), []))
  | MLfix _ as a ->
    (* Bare fixpoint in expression context — wrap in IIFE, delegate to gen_stmts. *)
    with_escape_analysis a (fun () ->
      CPPfun_call (CPPlambda([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false), []))
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLfloat f -> CPPfloat f
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic t -> gen_expr env t
  | MLdummy _ ->
    CPPabort "unreachable"
  | MLexn msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    CPPabort msg
  | MLaxiom s ->
    CPPabort ("unrealized axiom: " ^ s)
  | _ -> raise TODO

and eta_fun env f args =
  let rec get_eta_args dom args =
    match (dom, args) with
    | _::dom, _::args -> get_eta_args dom args
    | _ , _ -> dom in
  (* Check if an ML arg is a type class instance (a reference to a struct that implements a type class) *)
  let is_typeclass_instance_arg ml_arg =
    match ml_arg with
    | MLglob (r, _) ->
        (try
          let arg_ty = Table.find_type r in
          Table.is_typeclass_type arg_ty
        with Not_found -> false)
    | MLrel i ->
        (* Check if the referenced parameter is a type class instance *)
        (try
          let (db, _) = env in
          let _name = List.nth db (pred i) in
          (* Look up the type of this de Bruijn variable in the env's type context *)
          (* Check if the name matches our typeclass instance naming: _tcI0, _tcI1, etc. *)
          (* This is a heuristic - ideally we'd track types in the env *)
          let name_str = Id.to_string _name in
          String.length name_str >= 5 &&
          String.sub name_str 0 4 = "_tcI"
        with _ -> false)
    | MLapp (MLglob (r, _), _) ->
        (* Parameterized instance application, e.g. numList A H.
           Check if r's return type (after stripping Tarr) is a typeclass type. *)
        ref_returns_typeclass r
    | _ -> false
  in
  match f with
  | MLglob (id , tys) ->
    (* When the call has more args than the function's ML value-domain,
       the excess args are curried applications to the result.  This is common
       with Rocq's Function vernacular _correct proof terms, where the
       extraction produces e.g.  div2_rect f f0 f1 n _res __
       but div2_rect only has 4 value-domain params (f, f0, f1, n).
       The trailing _res and __ are applied to the result via currying.

       Split into:
       - primary_args: first n_value_dom args (passed to the function)
       - excess_args: remaining non-dummy args (curried onto the result)
       Only activates when n_args > n_value_dom; otherwise unchanged. *)
    let args, excess_args =
      let is_value_arg = function MLdummy _ -> false | _ -> true in
      let rec resolve_tmeta = function
        | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
        | t -> t
      in
      let rec collect_tarr_dom acc = function
        | Miniml.Tarr (t1, t2) -> collect_tarr_dom (resolve_tmeta t1 :: acc) t2
        | _ -> List.rev acc
      in
      try
        let ml_ty = Table.find_type id in
        let all_dom = collect_tarr_dom [] ml_ty in
        (* Skip leading Tdummy Ktype positions — these correspond to type args
           (tys), not value args. *)
        let rec skip_type_params = function
          | Miniml.Tdummy Miniml.Ktype :: rest -> skip_type_params rest
          | dom -> dom
        in
        let n_value_dom = List.length (skip_type_params all_dom) in
        let n_args = List.length args in
        if n_args > n_value_dom then
          let primary = List.filteri (fun i _ -> i < n_value_dom) args in
          let excess = List.filteri (fun i _ -> i >= n_value_dom) args in
          (List.filter is_value_arg primary, List.filter is_value_arg excess)
        else
          (args, [])
      with Not_found -> (args, [])
    in
    (* Partition args into type class instances and regular args *)
    let (typeclass_ml_args, regular_ml_args) =
      List.partition is_typeclass_instance_arg args in
    (* Reverse typeclass args to match template param order from gen_dfun:
       gen_dfun iterates collect_lams output (reversed from source) so the first
       typeclass in that order becomes 'i'. Call sites have args in source order,
       so we reverse to match. *)
    let typeclass_ml_args = List.rev typeclass_ml_args in
    (* Convert type class instance args to template type arguments *)
    let rec ml_arg_to_template_type ml_arg =
      match ml_arg with
      | MLglob (r, ts) ->
          (* Use the instance struct as a type - convert to Tglob *)
          Tglob (r, List.map (convert_ml_type_to_cpp_type env Refset'.empty []) ts, [])
      | MLrel i ->
          (* The instance is a lambda parameter - look up its name in the env
             and create a Tvar reference to the template parameter *)
          let (db, _) = env in
          let name = List.nth db (pred i) in
          Tvar (0, Some name)
      | MLapp (MLglob (r, ts), inner_args) ->
          (* Parameterized instance application, e.g. numList A H.
             Convert to Tglob(r, template_args, []) where template_args are
             built from the inner args. *)
          let template_args = List.filter_map (fun arg ->
            match arg with
            | MLdummy _ -> None  (* Erased type param — skip *)
            | _ -> Some (ml_arg_to_template_type arg)
          ) inner_args in
          Tglob (r, List.map (convert_ml_type_to_cpp_type env Refset'.empty []) ts @ template_args, [])
      | MLdummy _ -> Tany  (* Should not happen at top level, but be safe *)
      | _ -> assert false  (* Already filtered by is_typeclass_instance_arg *)
    in
    let typeclass_type_args = List.map ml_arg_to_template_type typeclass_ml_args in
    (* Filter out MLdummy entries from regular args — these are erased proof
       arguments that would generate CPPabort "unreachable" expressions and
       inflate the argument count for eta expansion. *)
    let regular_ml_args = List.filter (fun x -> match x with MLdummy _ -> false | _ -> true) regular_ml_args in
    (* Generate regular args as expressions *)
    let args = List.map (gen_expr env) regular_ml_args in
    let ty = find_type id in
    let ty = try (type_subst_list tys ty) with _ -> ty in (* TODO : make less hacky; do a type_subst that can't fail *)
    let tvars = get_current_type_vars () in
    let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ty in
    (* Combine: instance types first, then regular type args.
       If any regular type arg is Tany or a dummy type glob (from erased params),
       drop ALL regular type args via filter_erased_type_args and let the
       compiler deduce them.  See filter_erased_type_args for why we must drop
       all args rather than just the erased ones.

       Exception: when the callee's return type depends on an erased type var,
       C++ can't deduce it from lambda arguments (lambdas don't participate in
       template argument deduction).  In that case, recover the concrete type
       from the enclosing function's return type. *)
    let regular_type_args = List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys in
    (* Recover erased type args that C++ cannot deduce.
       Two cases:
       (a) tys is non-empty but all entries were erased (Tdummy Ktype) →
           filter_erased_type_args drops them all.
       (b) tys is empty — the Rocq extraction didn't supply type args at the
           call site, but the callee has Tdummy Ktype domain entries (erased
           type params).

       In both cases, if the callee's ML return type is a Tvar that refers to
       one of those erased type params, and we know the concrete return type
       from the enclosing function context (current_cpp_return_type), we can
       supply it as an explicit C++ template arg.

       This is needed because C++ cannot deduce template type params from
       lambda arguments — lambdas don't participate in template argument
       deduction. *)
    let regular_type_args =
      let filtered = filter_erased_type_args regular_type_args in
      (* Check if the callee's return type is a Tvar pointing to an erased
         (Tdummy Ktype) domain position, and if so, return the position index,
         the concrete C++ type to use, and the full ML domain. *)
      let try_recover_erased_return_type () =
        let rec resolve_tmeta = function
          | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
          | t -> t
        in
        match tctx.current_cpp_return_type with
        | None -> None
        | Some ret_ty ->
          match (try Some (Table.find_type id) with Not_found -> None) with
          | None -> None
          | Some ml_ty_orig ->
            let ret = resolve_tmeta (ml_return_type ml_ty_orig) in
            (match ret with
            | Miniml.Tvar i | Miniml.Tvar' i ->
              let rec collect_dom acc = function
                | Miniml.Tarr (t1, t2) -> collect_dom (resolve_tmeta t1 :: acc) t2
                | _ -> List.rev acc
              in
              let all_dom = collect_dom [] ml_ty_orig in
              (* Tvar uses 1-based indexing (matching type_subst_list);
                 convert to 0-based for list access. *)
              let idx = i - 1 in
              if idx >= 0 && idx < List.length all_dom then
                (match List.nth all_dom idx with
                | Miniml.Tdummy Miniml.Ktype -> Some (idx, ret_ty, all_dom)
                | _ -> None)
              else None
            | _ -> None)
      in
      if filtered = [] && regular_type_args <> [] then begin
        (* Case (a): tys was non-empty but all got filtered. *)
        match try_recover_erased_return_type () with
        | Some (idx, ret_ty, _) ->
          (* Replace the erased position with the concrete return type,
             then filter out any remaining erased entries. *)
          List.mapi (fun j t -> if j = idx then ret_ty else t) regular_type_args
          |> List.filter (fun t -> not (is_erased_type t))
        | None -> filtered
      end
      else if tys = [] then begin
        (* Case (b): tys is empty — synthesize type args from scratch.
           Build one entry per Tdummy Ktype domain position. *)
        match try_recover_erased_return_type () with
        | Some (_idx, ret_ty, all_dom) ->
          List.filter_map (function
            | Miniml.Tdummy Miniml.Ktype -> Some ret_ty
            | _ -> None
          ) all_dom
        | None -> filtered
      end
      else filtered
    in
    let all_type_args = typeclass_type_args @ regular_type_args in
    let cglob = mk_cppglob id all_type_args in
    (* Check if this is a typeclass instance used as a type (for :: access).
       When all args are consumed (domain and args both empty after filtering),
       return just the type reference, not a function call. This avoids
       generating numOption<numNat, unsigned int>() instead of
       numOption<numNat, unsigned int> for qualified access like ::to_nat. *)
    let id_is_typeclass_instance = ref_returns_typeclass id in
    (* Curried excess args (see split above) indicate a call pattern like
       div2_rect(f,f0,f1,n)(_res) from Rocq's Function vernacular _correct
       proof terms.  The intermediate return type would need to be a
       std::function, and the lambda arguments would need restructuring to
       match — neither of which the current translation supports.  Since
       these proof-certificate functions are never called at runtime,
       generate an abort placeholder. *)
    if excess_args <> [] then
      CPPabort "untranslatable curried proof term"
    else
    (match ty with
    | Tfun (dom, cod) ->
      (* Filter domain to exclude type class types (they're now template params)
         and erased types.  Use has_hkt_erasure for deep checking: proof params
         like wf witnesses may extract as function types containing dummy_type
         (e.g. Tfun([List<T1>], dummy_type)) rather than plain dummy_type.
         These entries must be removed to match the ML arg list which already
         filters out MLdummy entries. *)
      let dom = List.filter (fun t -> not (Table.is_typeclass_type_cpp t) && not (is_erased_type t)) dom in
      let missing_args = get_eta_args dom args in
      if missing_args == [] then begin
        if id_is_typeclass_instance && args = [] then
          (* Typeclass instance with no regular args — return as a type reference *)
          cglob
        else
          CPPfun_call (cglob, List.rev args)
      end else
      let eta_args = List.mapi (fun i ty -> (Tmod (TMconst, ty), Some (Id.of_string ("_x" ^ string_of_int i)))) missing_args in
      let call_args = args @
         List.mapi (fun i _ -> (CPPvar (Id.of_string ("_x" ^ string_of_int i)))) eta_args in
      CPPlambda (List.rev eta_args, None,[Sreturn (Some (CPPfun_call (cglob, List.rev call_args)))], false)
    | _ ->
      if id_is_typeclass_instance && args = [] then
        cglob
      else
        CPPfun_call (cglob, args))
  | _ ->
    (* Non-global callee (e.g., a local variable from MLrel).  Filter out
       MLdummy args — these are erased type/prop parameters that have no
       runtime representation.  Unlike the MLglob case above, there is no
       type-arg list to filter here; we only need to drop value-level dummies. *)
    let args = List.filter (fun x -> match x with MLdummy _ -> false | _ -> true) args in
    let args = List.map (fun x -> (gen_expr env x)) args in
    CPPfun_call (gen_expr env f, List.rev args)

and gen_cpp_pat_lambda env (typ : ml_type) rty cname ids dummies body =
  (* Get type variables in scope from enclosing function's template parameters *)
  let tvars = get_current_type_vars () in
  (* Get the constructor name as a simple Id *)
  let ctor_name = match cname with
    | GlobRef.ConstructRef _ -> Id.of_string (Common.pp_global_name Type cname)
    | _ -> Id.of_string "unknown_ctor"
  in
  (* Build path: typename InductiveType<temps>::ConstructorName *)
  let constr = match typ with
  | Tglob (r, tys, _) ->
    let tys = List.map type_simpl tys in
    (* Filter out index type args - only keep parameters *)
    let tys = match r with
      | GlobRef.IndRef (kn, _) ->
          (match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars -> List.firstn num_param_vars tys
          | None -> tys)
      | _ -> tys
    in
    let temps = List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys in
    (* The constructor struct is nested inside the inductive type *)
    (* Generate: typename list<unsigned int>::nil *)
    (* Build the full inductive type first, then qualify with the constructor name *)
    (* For local inductives (defined in current module), don't wrap in Tnamespace
       to avoid double qualification like tree::tree::Empty *)
    let is_local_ind = List.exists (Environ.QGlobRef.equal Environ.empty_env r) (get_local_inductives ()) in
    let ind_type = if is_local_ind then Tglob (r, temps, []) else Tnamespace (r, Tglob (r, temps, [])) in
    Tqualified (ind_type, ctor_name)
  | _ -> Tid (ctor_name, []) in
  let sname = Id.of_string "_args" in
  (* Check if this is an indexed inductive (has indices but no params).
     Only erase Tvars for constructor field types, NOT for the function's return type.
     The return type's Tvars come from the function's template params, not the inductive's indices. *)
  let is_indexed_ind = match typ with
    | Tglob (GlobRef.IndRef (kn, _), tys, _) ->
        (* It's indexed if: there are type args (indices) AND no param vars *)
        tys <> [] &&
        (match Table.get_ind_num_param_vars_opt kn with
        | Some 0 -> true
        | _ -> false)
    | _ -> false
  in
  let ret = convert_ml_type_to_cpp_type env Refset'.empty tvars rty in
  (* For pattern matching lambdas, use 'auto' when the return type can't be
     expressed as a valid C++ type annotation:
     - Unnamed Tvar (T1, T2 not in template params): unresolvable
     - Tfun (std::function<...>): often contains dependent types like T1(...)
       that cause parsing ambiguities in lambda trailing return types *)
  let ret = match ret with
    | Minicpp.Tvar (_, None) -> Minicpp.Ttodo  (* Ttodo prints as 'auto' *)
    | Minicpp.Tfun _ -> Minicpp.Ttodo  (* C++ can deduce the return type *)
    | _ -> ret
  in
  let asgns =  List.mapi (fun i x ->
      let id = Id.of_string ("_a" ^ string_of_int i) in
      let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars (snd x) in
      (* Only erase Tvars in constructor field types for indexed inductives *)
      let cpp_ty = if is_indexed_ind then tvar_erase_type cpp_ty else cpp_ty in
      (* Use 'auto' for unresolved type variables in non-template contexts.
         This handles cases where MLcase type annotations have Tvar/Tvar' that
         can't be resolved (e.g., sig's type parameter in Function vernacular).
         Check for Tvar(_, None) at any depth: a top-level Tvar(_, None) becomes
         auto directly; a nested one (e.g. Tshared_ptr(Tglob(list, [Tvar(1, None)])))
         must also become auto since List<auto> is invalid C++. *)
      let cpp_ty = if tvars = [] && has_unnamed_tvar cpp_ty then Minicpp.Ttodo else cpp_ty in
      Sasgn (fst x, Some cpp_ty, CPPget (mk_cppglob_local (GlobRef.VarRef sname) [], id))) (List.rev ids) in
  let asgns = List.filteri (fun i _ -> List.nth dummies i) asgns in
  (* Phase 2: Add pattern-bound variables as owned for move insertion.
     Pattern variables are extracted from the scrutinee into local variables,
     so they own their values. ids is in de Bruijn order. *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let n_pat_vars = List.length ids in
  let pat_owned = Escape.IntSet.of_list (List.filter_map (fun i ->
    let db = i + 1 in
    let (_, ml_ty) = List.nth ids i in
    if Escape.is_shared_ptr_type ml_ty then Some db else None
  ) (List.init n_pat_vars (fun i -> i))) in
  (* Shift existing owned vars by n_pat_vars (pattern vars add binders) *)
  let shifted_outer = Escape.IntSet.map (fun i -> i + n_pat_vars) tctx.move_owned_vars in
  tctx.move_owned_vars <- Escape.IntSet.union pat_owned shifted_outer;
  tctx.move_dead_after <- Escape.IntSet.empty;
  let body_stmts = gen_stmts env (fun x -> Sreturn (Some x)) body in
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  CPPlambda(
        [(Tmod (TMconst, constr), Some sname)],
        Some ret,
        asgns @ body_stmts, false)

and gen_cpp_case (typ : ml_type) t env pv =
  (* When the match type annotation has unresolved Tvars, try to resolve from context.
     This handles monomorphic functions where MLcase has Tvar but the concrete type is known. *)
  let resolve_tvar_type typ candidate =
    match typ, candidate with
    | Miniml.Tglob (r1, _, _), Miniml.Tglob (r2, _, _)
      when Environ.QGlobRef.equal Environ.empty_env r1 r2
        && has_tvar typ && not (has_tvar candidate) ->
        candidate
    | _ -> typ
  in
  let typ = match t with
    | MLrel i | MLmagic (MLrel i) ->
        (* Scrutinee is a variable reference — use its concrete type.
           Try env_types first (correctly tracks let-bound variables with
           shifted de Bruijn indices), then fall back to param_types.
           Unwrap Tmeta wrappers since env_types may store types in Tmeta form. *)
        let rec unwrap_tmeta = function
          | Miniml.Tmeta { contents = Some t } -> unwrap_tmeta t
          | t -> t
        in
        let env_ty_opt = try
          let env_ty = unwrap_tmeta (get_env_type i) in
          (match env_ty with Miniml.Tglob _ -> Some env_ty | _ -> None)
        with _ -> None in
        (match env_ty_opt with
         | Some let_ty -> resolve_tvar_type typ let_ty
         | None ->
             (match get_param_type_by_index i with
              | Some (Miniml.Tglob _ as param_ty) -> resolve_tvar_type typ param_ty
              | _ -> typ))
    | MLapp (func_expr, _) | MLmagic (MLapp (func_expr, _)) ->
        (* Scrutinee is a function call — use function's return type *)
        let func_ref = match func_expr with
          | MLglob (r, _) | MLmagic (MLglob (r, _)) -> Some r
          | _ -> None
        in
        (match func_ref with
         | Some r ->
             (try
               let ret_ty = ml_return_type (Table.find_type r) in
               resolve_tvar_type typ ret_ty
             with Not_found -> typ)
         | None -> typ)
    | _ -> typ
  in
  (* Check if this is an enum inductive type *)
  let is_enum = match typ with
    | Miniml.Tglob (GlobRef.IndRef (kn, i), _, _) -> is_enum_inductive (GlobRef.IndRef (kn, i))
    | _ -> false
  in
  if is_enum then
    (* Generate switch-based matching wrapped in IIFE *)
    let ind_ref = match typ with
      | Miniml.Tglob (r, _, _) -> r
      | _ -> assert false
    in
    let scrutinee = gen_expr env t in
    let rec gen_enum_branches = function
      | [] -> []
      | (ids, _rty, p, body) :: cs ->
        (match p with
        | Pusual r | Pcons (r, _) ->
          let _ids', env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
          let ctor_name = Id.of_string (Common.pp_global_name Type r) in
          let body_stmts = gen_stmts env' (fun x -> Sreturn (Some x)) body in
          (ctor_name, body_stmts) :: gen_enum_branches cs
        | Pwild | Prel _ | Ptuple _ ->
          gen_enum_branches cs)
    in
    let branches = gen_enum_branches (Array.to_list pv) in
    CPPfun_call (CPPlambda ([], None, [Sswitch (scrutinee, ind_ref, branches)], false), [])
  else
  (* Phase 3: Check for reuse opportunities (reset/reuse).
     If the scrutinee is an owned shared_ptr variable and there are reuse
     candidates (branches that construct same-type, same-arity values),
     generate a dual-path: reuse when use_count()==1, normal std::visit otherwise. *)
  let reuse_candidates = Escape.find_reuse_candidates typ pv in
  let scrut_db = match t with MLrel i -> Some i | MLmagic (MLrel i) -> Some i | _ -> None in
  let scrut_is_owned = match scrut_db with
    | Some i -> Escape.IntSet.mem i tctx.move_owned_vars
    | None -> false
  in
  (* Helper: generate the normal std::visit path *)
  let gen_normal_visit_expr () =
    let outer cases x = (CPPfun_call (CPPvisit, CPPmethod_call (x, Id.of_string "v", []) :: [CPPoverloaded cases])) in
    let rec gen_cases = function
    | [] -> []
    | (ids,rty,p,t) :: cs ->
      (match p with
      | Pusual r | Pcons (r, _) ->
        let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
        let saved_env_types = tctx.env_types in
        push_env_types ids';
        let dummies = List.map (fun (x,_) ->
          match x with
          | Dummy -> false
          | _ -> true) ids in
        let br = gen_cpp_pat_lambda env' typ rty r ids' dummies t in
        tctx.env_types <- saved_env_types;
        br :: (gen_cases cs)
      | Pwild | Prel _ | Ptuple _ ->
        gen_cases cs) in
    outer (gen_cases (Array.to_list pv)) (gen_expr env t)
  in
  (* Also exclude coinductive types — they use lazy evaluation and don't have v_mut(). *)
  let is_coinductive = is_coinductive_type typ in
  if reuse_candidates <> [] && scrut_is_owned && not is_coinductive then begin
    (* Generate dual-path code wrapped in IIFE:
       if (scrut.use_count() == 1 && scrut->v().index() == N) {
         // reuse path: mutate in place
       } else {
         // normal std::visit path
       } *)
    let scrut_expr = gen_expr env t in
    let tvars = get_current_type_vars () in
    (* For now, handle the first reuse candidate only. *)
    let (branch_idx, _matched_ctor, arity, _tail_ctor, tail_args) = List.hd reuse_candidates in
    let (ids, _rty, _pat, body) = pv.(branch_idx) in
    let n_fields = arity in
    (* Build the condition: scrut.use_count() == 1 && scrut->v().index() == N
       Using proper AST nodes (CPPbinop, CPPmember, CPPmethod_call) so that
       variable substitution (e.g., l -> this for methods) works correctly. *)
    let use_count_call = CPPfun_call (CPPmember (scrut_expr, Id.of_string "use_count"), []) in
    let index_call = CPPfun_call (
      CPPmember (CPPmethod_call (scrut_expr, Id.of_string "v", []), Id.of_string "index"), []) in
    let cond = CPPbinop ("&&",
      CPPbinop ("==", use_count_call, CPPraw "1"),
      CPPbinop ("==", index_call, CPPraw (string_of_int branch_idx))) in
    (* Build the reuse body *)
    (* 1. Get mutable reference to the variant alternative:
          auto& _rf = std::get<N>(scrut->v_mut()); *)
    let rf_var = Id.of_string "_rf" in
    let get_field_ref = Sasgn (rf_var, Some (Tref (Ttodo)),
      CPPfun_call (CPPraw ("std::get<" ^ string_of_int branch_idx ^ ">"),
        [CPPmethod_call (scrut_expr, Id.of_string "v_mut", [])])) in
    (* 2. Push pattern variables into the environment, same as normal path *)
    let ids' , env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
    let saved_env_types = tctx.env_types in
    push_env_types ids';
    (* 3. Extract fields into local variables:
          auto var_name = std::move(_rf._aN);
       Use ids' (renamed, same order as gen_cpp_pat_lambda) so that:
       - Variable names match what gen_expr/body_env expects (renamed names)
       - Field indices match constructor field order after List.rev *)
    let dummies = List.rev_map (fun (x, _) -> match x with Dummy -> false | _ -> true) ids in
    let rev_ids' = List.rev ids' in
    let extract_stmts = List.mapi (fun i (var_name, ml_ty) ->
      let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty in
      if List.nth dummies i then
        Some (Sasgn (var_name, Some cpp_ty,
          CPPmove (CPPmember (CPPvar (Id.of_string "_rf"), Id.of_string ("_a" ^ string_of_int i)))))
      else None
    ) rev_ids' in
    let extract_stmts = List.filter_map Fun.id extract_stmts in
    (* 4. Generate intermediate let bindings from the body, if any.
       Walk through MLletin/MLmagic to reach the tail MLcons, generating
       statements for each intermediate binding. *)
    let rec gen_prefix_and_tail env' body =
      match body with
      | MLcons (_, _, _) ->
          (* Reached the tail constructor — no more prefix *)
          ([], env')
      | MLmagic a -> gen_prefix_and_tail env' a
      | MLletin (x, t, a, b) ->
          let x' = remove_prime_id (id_of_mlid x) in
          let _, env'' = push_vars' [x', t] env' in
          push_env_types [x', t];
          let afun v = Sasgn (x', None, v) in
          let asgn = gen_stmts env' afun a in
          let letin_stmt = match asgn with
            | [ Sasgn (x', None, e) ] ->
                [Sasgn (x', Some (convert_ml_type_to_cpp_type env Refset'.empty tvars t), e)]
            | _ ->
                Sdecl (x', convert_ml_type_to_cpp_type env Refset'.empty tvars t) :: asgn
          in
          let (rest, final_env) = gen_prefix_and_tail env'' b in
          (letin_stmt @ rest, final_env)
      | _ -> ([], env')  (* shouldn't happen for reuse candidates *)
    in
    let (prefix_stmts, body_env) = gen_prefix_and_tail env' body in
    (* 5. Compute new field values and assign them back:
          _rf._aN = <new_value>; *)
    let assign_stmts = List.mapi (fun i tail_arg ->
      let field_id = Id.of_string ("_a" ^ string_of_int i) in
      let new_val = gen_expr body_env tail_arg in
      Sassign_field (CPPvar (Id.of_string "_rf"), field_id, new_val)
    ) tail_args in
    (* 6. Return the original scrutinee (reusing the memory cell) *)
    let return_scrut = Sreturn (Some scrut_expr) in
    let reuse_stmts =
      [get_field_ref] @ extract_stmts @ prefix_stmts @ assign_stmts @ [return_scrut] in
    (* Build the else branch: normal std::visit *)
    let normal_visit = Sreturn (Some (gen_normal_visit_expr ())) in
    (* Generate IIFE with if-else *)
    let _ = n_fields in
    tctx.env_types <- saved_env_types;
    CPPfun_call (CPPlambda ([], None,
      [Sif (cond, reuse_stmts, [normal_visit])], false), [])
  end else
  gen_normal_visit_expr ()

and gen_cpp_custom_body env k rty ids body =
  let tvars = get_current_type_vars () in
  let ret = convert_ml_type_to_cpp_type env Refset'.empty tvars rty in
  let ids =  List.map (fun (x, ty) -> (x, convert_ml_type_to_cpp_type env Refset'.empty tvars ty)) (List.rev ids) in
  let body = gen_stmts env k body in
  (ids, ret, body)

and gen_custom_cpp_case env k (typ : ml_type) t pv =
  let tvars = get_current_type_vars () in
  let temps = match typ with
  | Tglob (r, tys, _) ->
    List.map (convert_ml_type_to_cpp_type env Refset'.empty tvars) tys
  | _ -> [] in
  let typ = convert_ml_type_to_cpp_type env Refset'.empty tvars typ in
  let t = gen_expr env t in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r | Pcons (r, _) ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let saved_env_types = tctx.env_types in
      push_env_types ids';
      let br = gen_cpp_custom_body env' k rty ids' t in
      tctx.env_types <- saved_env_types;
      br :: (gen_cases cs)
    | Pwild | Prel _ | Ptuple _ ->
      gen_cases cs) in
  let cmatch = find_custom_match pv in
  Scustom_case (typ, t, temps, gen_cases (Array.to_list pv), cmatch)

and gen_stmts env (k : cpp_expr -> cpp_stmt) ast =
  match ast with
| MLletin (_, _, MLfix (x, ids, funs, _), b) as _whole ->
  (* Special case for let-fix: the let binding name is the fix function name *)
  (* Resolve unresolved metas in fix function types to Tvars using mgu. *)
  let next_tvar = ref 1 in
  let rec resolve_metas = function
    | Miniml.Tmeta ({ contents = None } as m) ->
        let idx = !next_tvar in next_tvar := idx + 1;
        try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
    | Miniml.Tmeta { contents = Some t } -> resolve_metas t
    | Miniml.Tarr (t1, t2) -> resolve_metas t1; resolve_metas t2
    | Miniml.Tglob (_, args, _) -> List.iter resolve_metas args
    | _ -> () in
  Array.iter (fun (_, ty) -> resolve_metas ty) ids;
  (* Collect all Tvar indices from the fixpoint types *)
  let fix_tvar_indices = Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids in
  let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
  let outer_tvars = get_current_type_vars () in
  let n_outer = List.length outer_tvars in
  (* Check if fixpoint introduces Tvars beyond the outer scope *)
  let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
  if has_extra_tvars then begin
    (* Lift the polymorphic inner fixpoint to a top-level function.
       Build tvar names for all Tvars used in the fixpoint type:
       - Tvars 1..n_outer reuse the outer function's template param names
       - Tvars beyond n_outer get fresh names T<i> *)
    let all_tvar_names = List.map (fun i ->
      if i <= n_outer then
        List.nth outer_tvars (i - 1)
      else
        Id.of_string ("T" ^ string_of_int i)
    ) fix_tvar_indices in
    let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
    (* Generate the lifted function name *)
    let fix_name = fst (ids.(x)) in
    let outer_name = match tctx.current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
    (* Save and set current_type_vars to the full tvar list for the lifted function *)
    let saved_tvars = get_current_type_vars () in
    set_current_type_vars all_tvar_names;
    (* Generate the fixpoint body using gen_fix, passing all mutual fixpoint names *)
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled = Array.to_list (Array.mapi (fun i f ->
      gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f) funs) in
    (* Restore outer type vars *)
    set_current_type_vars saved_tvars;
    (* Build a lifted Dfundef for each fixpoint function (usually just one) *)
    List.iteri (fun i ((renamed_id, fix_ty), params, body) ->
      let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names fix_ty in
      let (_, cod) = match cpp_ty with
        | Tfun (dom, cod) -> (dom, cod)
        | _ -> ([], cpp_ty) in
      let (cpp_params, all_temps_with_funs) =
        build_lifted_cpp_params (convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names) all_temps params in
      (* Replace recursive self-references (CPPvar renamed_n) with calls to the lifted function *)
      let rec_call = mk_cppglob lifted_ref (List.map (fun id -> Tvar (0, Some id)) all_tvar_names) in
      let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
      let inner = Dfundef ([lifted_ref, []], cod, cpp_params, body) in
      let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
      add_lifted_decl lifted_decl
    ) funs_compiled;
    (* In the continuation body b, the fixpoint name should resolve to a call
       to the lifted function with appropriate type arguments.
       We push the fix name into the env so that MLrel references in b resolve correctly. *)
    let fix_ids_for_env = Array.to_list (Array.map (fun (n, ty) -> (n, ty)) ids) in
    let _, env_with_fix = push_vars' fix_ids_for_env env in
    push_env_types fix_ids_for_env;
    (* Generate b, then replace references to the fixpoint var with calls to the lifted function.
       Build explicit type args: outer tvars stay as Tvar references, extra tvars
       are resolved to concrete types from the enclosing function's return type. *)
    let call_type_args =
      let extra_tvar_names = List.filter (fun id ->
        not (List.exists (Id.equal id) outer_tvars)) all_tvar_names in
      if extra_tvar_names = [] then
        List.map (fun id -> Tvar (0, Some id)) outer_tvars
      else begin
        let fix_ty = snd ids.(0) in
        let tmpl_cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names fix_ty in
        let tmpl_cod = match tmpl_cpp_ty with
          | Tfun (_, cod) -> cod | t -> t in
        let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
        let extra_args = List.map (fun tvar_name ->
          match tmpl_cod with
          | Tvar (_, Some id) when Id.equal id tvar_name ->
            (match tctx.current_cpp_return_type with
             | Some ret_ty -> ret_ty
             | None -> Tvar (0, Some tvar_name))
          | _ ->
            (match tctx.current_cpp_return_type with
             | Some ret_ty -> ret_ty
             | None -> Tvar (0, Some tvar_name))
        ) extra_tvar_names in
        outer_args @ extra_args
      end
    in
    let lifted_call = mk_cppglob lifted_ref call_type_args in
    (* Phase 2: shift owned vars for fix bindings *)
    let n_fix_bindings_lifted = Array.length ids in
    let saved_owned_lifted = tctx.move_owned_vars in
    tctx.move_owned_vars <- Escape.IntSet.map (fun i -> i + n_fix_bindings_lifted) tctx.move_owned_vars;
    let result = gen_stmts env_with_fix k b in
    tctx.move_owned_vars <- saved_owned_lifted;
    List.map (local_var_subst_stmt fix_name lifted_call) result
  end else begin
    (* No extra Tvars - proceed with original local fixpoint approach *)
    (* Call gen_fix with all mutual fixpoint names so each body can reference the others *)
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled = Array.to_list (Array.mapi (fun i f ->
      gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f) funs) in
    (* Extract the renamed ids from gen_fix results *)
    let renamed_ids = List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled in
    let funs_with_params = List.map (fun (_, params, body) -> (params, body)) funs_compiled in
    let tvars = get_current_type_vars () in
    (* For std::function declarations, if return type is an unnamed Tvar, use void as placeholder. *)
    let fix_func_type ty =
      match ty with
      | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
          Minicpp.Tfun (params, Minicpp.Tvoid)
      | _ -> ty
    in
    (* Use renamed ids for declarations *)
    let decls = List.map (fun (id, ty) ->
      Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env Refset'.empty tvars ty))) renamed_ids in
    let ret_ty ty = (match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
      | Tfun (_,t) ->
          (match t with
          | Minicpp.Tvar (_, None) -> None
          | _ -> Some t)
      | _ -> None) in
    (* Use renamed ids for definitions *)
    let defs = List.map2 (fun (id, fty) (args, body) ->
      Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id) args, ret_ty fty, body, false))) renamed_ids funs_with_params in
    (* Add renamed ids to environment for processing body *)
    let _, env_with_fix = push_vars' renamed_ids env in
    push_env_types renamed_ids;
    (* Phase 2: shift owned vars for fix bindings *)
    let n_fix_bindings = Array.length ids in
    let saved_owned = tctx.move_owned_vars in
    tctx.move_owned_vars <- Escape.IntSet.map (fun i -> i + n_fix_bindings) tctx.move_owned_vars;
    let cont = gen_stmts env_with_fix k b in
    tctx.move_owned_vars <- saved_owned;
    decls @ defs @ cont
  end
| MLletin (x, t, (MLlam _ as a), b) ->
  (* Check if this is a polymorphic lambda that should be lifted to a top-level template function. *)
  let next_tvar = ref 1 in
  let rec resolve_metas = function
    | Miniml.Tmeta ({ contents = None } as m) ->
        let idx = !next_tvar in next_tvar := idx + 1;
        try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
    | Miniml.Tmeta { contents = Some t } -> resolve_metas t
    | Miniml.Tarr (t1, t2) -> resolve_metas t1; resolve_metas t2
    | Miniml.Tglob (_, args, _) -> List.iter resolve_metas args
    | _ -> () in
  resolve_metas t;
  resolve_metas_in_ast resolve_metas a;
  (* Collect all Tvar indices from the let-binding type *)
  let tvar_indices = collect_tvars [] t in
  (* Also collect Tvars from the lambda body *)
  let body_tvars = collect_tvars_ast [] a in
  let all_body_tvars = List.sort_uniq Int.compare body_tvars in
  let tvar_indices = List.sort Int.compare tvar_indices in
  let outer_tvars = get_current_type_vars () in
  let n_outer = List.length outer_tvars in
  let has_extra = List.exists (fun i -> i > n_outer) tvar_indices in
  (* Normal MLletin fallback (shared by no-extra-tvars and thunk-with-free-vars cases) *)
  let gen_normal_letin () =
    let x' = remove_prime_id (id_of_mlid x) in
    let renamed_ids,env' = push_vars' [x', t] env in
    let x_renamed = fst (List.hd renamed_ids) in
    push_env_types [x_renamed, t];
    if x == Dummy then gen_stmts env' k b else
    let afun v = Sasgn (x_renamed, None, v) in
    let asgn = gen_stmts env afun a in
    let tvars = get_current_type_vars () in
    (* Phase 2: shift owned vars for lambda let binding *)
    let saved_owned_lam = tctx.move_owned_vars in
    tctx.move_owned_vars <- Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
    let gen_cont () =
      let cont = gen_stmts env' k b in
      tctx.move_owned_vars <- saved_owned_lam;
      cont
    in
    match asgn with
    | [ Sasgn (_, None, e) ] -> Sasgn (x_renamed, Some (convert_ml_type_to_cpp_type env Refset'.empty tvars t), e) :: gen_cont ()
    | _ ->
      Sdecl (x_renamed, convert_ml_type_to_cpp_type env Refset'.empty tvars t) :: asgn @ gen_cont ()
  in
  if not has_extra then gen_normal_letin ()
  else begin
    (* Lift the polymorphic lambda to a top-level template function. *)
    let params, body = collect_lams a in
    let n_params = List.length params in
    let x' = remove_prime_id (id_of_mlid x) in

    (* 1. Collect free variables in the lambda body *)
    let free_indices = collect_free_rels n_params body in
    let free_vars = List.map (fun i ->
      let name = get_db_name i env in
      let ty = get_env_type i in
      (name, ty, i)
    ) (List.sort Int.compare free_indices) in

    (* Check if all parameters are dummy/void - if so, this is likely a thunk for monadic ops *)
    let all_params_dummy = List.for_all (fun (_, ty) -> isTdummy ty || ml_type_is_void ty) params in

    (* Don't lift thunks (all-dummy params) that capture free variables - these are typically
       for monadic operations where the lambda is passed to a higher-order function that
       immediately invokes it, and lifting creates type mismatches. *)
    if free_vars <> [] && all_params_dummy then gen_normal_letin ()
    else begin

    (* 2. Build tvar names: outer tvars keep their names, extra tvars get fresh names *)
    let all_tvar_names = List.map (fun i ->
      if i <= n_outer then
        List.nth outer_tvars (i - 1)
      else
        Id.of_string ("T" ^ string_of_int i)
    ) tvar_indices in
    let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in

    let extended_tvar_names = build_extended_tvar_names tvar_indices all_tvar_names all_body_tvars in

    (* 3. Generate the lifted function name *)
    let outer_name = match tctx.current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string x' in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in

    (* 4. Substitution helper for call sites: replace CPPfun_call(CPPvar x', args) with
       CPPfun_call(CPPglob(lifted_ref, []), free_var_cpps @ args) *)
    let rec subst_lifted_call_expr (target : Id.t) (lifted : GlobRef.t) (free_args : cpp_expr list) (e : cpp_expr) =
      let sub = subst_lifted_call_expr target lifted free_args in
      match e with
      | CPPfun_call (CPPvar id, args) when Id.equal id target ->
          CPPfun_call (mk_cppglob lifted [], free_args @ List.map sub args)
      | CPPvar id when Id.equal id target ->
          (* Bare reference to lifted function: if there are free args, wrap in a lambda *)
          if free_args = [] then
            mk_cppglob lifted []
          else
            (* Generate a lambda that captures and forwards: [&]() { return lifted(free_args...); } *)
            CPPlambda ([], None, [Sreturn (Some (CPPfun_call (mk_cppglob lifted [], free_args)))], false)
      | CPPfun_call (f, args) -> CPPfun_call (sub f, List.map sub args)
      | CPPderef e' -> CPPderef (sub e')
      | CPPmove e' -> CPPmove (sub e')
      | CPPlambda (args, ty, b, cbv) -> CPPlambda (args, ty, List.map (subst_lifted_call_stmt target lifted free_args) b, cbv)
      | CPPoverloaded cases -> CPPoverloaded (List.map sub cases)
      | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map sub args)
      | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map sub args)
      | CPPget (e', id') -> CPPget (sub e', id')
      | CPPget' (e', id') -> CPPget' (sub e', id')
      | CPPnamespace (id', e') -> CPPnamespace (id', sub e')
      | CPPparray (args, e') -> CPPparray (Array.map sub args, sub e')
      | CPPmethod_call (obj, meth, args) -> CPPmethod_call (sub obj, meth, List.map sub args)
      | CPPmember (e', mid) -> CPPmember (sub e', mid)
      | CPParrow (e', mid) -> CPParrow (sub e', mid)
      | CPPforward (ty, e') -> CPPforward (ty, sub e')
      | CPPnew (ty, args) -> CPPnew (ty, List.map sub args)
      | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ty, sub e')
      | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, tys, List.map sub args)
      | CPPqualified (e', qid) -> CPPqualified (sub e', qid)
      | _ -> e
    and subst_lifted_call_stmt (target : Id.t) (lifted : GlobRef.t) (free_args : cpp_expr list) (s : cpp_stmt) =
      match s with
      | Sreturn (Some e) -> Sreturn (Some (subst_lifted_call_expr target lifted free_args e))
      | Sreturn None -> Sreturn None
      | Sasgn (id, ty, e) -> Sasgn (id, ty, subst_lifted_call_expr target lifted free_args e)
      | Sexpr e -> Sexpr (subst_lifted_call_expr target lifted free_args e)
      | Scustom_case (ty, e, tys, brs, str) ->
          Scustom_case (ty, subst_lifted_call_expr target lifted free_args e, tys,
            List.map (fun (args, ty, stmts) ->
              (args, ty, List.map (subst_lifted_call_stmt target lifted free_args) stmts)) brs, str)
      | _ -> s
    in

    (* 6. Compile the lambda body with extended type variables *)
    let saved_tvars = get_current_type_vars () in
    set_current_type_vars extended_tvar_names;
    (* Push lambda params into env for body compilation *)
    let param_ids = List.map (fun (ml_id, ty) -> (remove_prime_id (id_of_mlid ml_id), ty)) params in
    (* For free variables, we need to adjust de Bruijn indices in the body.
       The body references free vars as MLrel (n_params + i) where i is the outer index.
       We compile with an env that has: [free_var_params...; lambda_params...]
       So we push free var names first, then lambda param names. *)
    let free_var_params = List.map (fun (name, ty, _) -> (name, ty)) free_vars in
    let body_params_for_env = free_var_params @ param_ids in
    let body_param_ids, body_env = push_vars' body_params_for_env env in
    let saved_env_types = tctx.env_types in
    push_env_types body_param_ids;

    (* Now compile the body. The body's de Bruijn indices:
       MLrel 1..n_params -> lambda params (at positions n_free+1..n_free+n_params in our env)
       MLrel n_params+i -> free var i (should map to position n_free-i+1 in our env, but
         we actually need to adjust: MLrel (n_params + orig_outer_idx) in the body maps to
         outer env position orig_outer_idx. In our extended env, free vars are at positions
         n_params+1..n_params+n_free. So we need to remap.
       Actually, the body already has correct de Bruijn indices:
       - MLrel 1..n_params are the lambda params
       - MLrel (n_params + i) references outer scope position i
       When we push [free_var_params @ param_ids], the env has:
         positions 1..n_params = param_ids (lambda params)
         positions n_params+1..n_params+n_free = free_var_params
       But the body references MLrel(n_params + original_outer_idx), and original_outer_idx
       may not equal the position in free_var_params.
       We need the body env to map MLrel(n_params + i) correctly for each free var. *)

    (* Simpler approach: compile body in a modified env where free vars at their original
       positions are accessible. We push only the lambda params on top of the outer env. *)
    let lam_param_ids, lam_env = push_vars' param_ids env in
    tctx.env_types <- saved_env_types;
    push_env_types lam_param_ids;
    let compiled_body = gen_stmts lam_env (fun x -> Sreturn (Some x)) body in
    tctx.env_types <- saved_env_types;
    set_current_type_vars saved_tvars;

    (* 7. Now substitute free variable references in compiled body:
       Free vars in the body were compiled as CPPvar(name_from_outer_env).
       In the lifted function, they become parameters. The names are the same,
       so no substitution of the body is needed — the free var params have the same
       names as the outer scope variables. *)

    (* 8. Build the lifted function parameters: free vars first, then lambda params *)
    let all_lifted_params = free_var_params @ (List.filter (fun (_, ty) -> not (ml_type_is_void ty) && not (isTdummy ty)) lam_param_ids) in
    let (cpp_params, all_temps_with_funs) =
      build_lifted_cpp_params (convert_ml_type_to_cpp_type lam_env Refset'.empty extended_tvar_names) all_temps all_lifted_params in

    (* Get return type from the let-binding type *)
    let cpp_ty = convert_ml_type_to_cpp_type lam_env Refset'.empty extended_tvar_names t in
    let cod = match cpp_ty with
      | Tfun (_, cod) -> cod
      | _ -> cpp_ty in

    (* 9. Build and register the lifted declaration *)
    let inner = Dfundef ([lifted_ref, []], cod, cpp_params, compiled_body) in
    let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
    add_lifted_decl lifted_decl;

    (* 10. Compile the continuation body b, substituting calls to x' with calls to the lifted function *)
    let ids_renamed2, env' = push_vars' [x', t] env in
    let x_renamed2 = fst (List.hd ids_renamed2) in
    push_env_types [x_renamed2, t];
    (* Phase 2: shift owned vars for lifted lambda binding *)
    let saved_owned_lifted2 = tctx.move_owned_vars in
    tctx.move_owned_vars <- Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
    let cont = gen_stmts env' k b in
    tctx.move_owned_vars <- saved_owned_lifted2;
    (* Build the free variable argument expressions *)
    let free_var_cpps = List.map (fun (name, _, _) -> CPPvar name) free_vars in
    List.map (subst_lifted_call_stmt x_renamed2 lifted_ref free_var_cpps) cont
    end
  end
| MLletin (x, t, a, b) ->
  let x' = remove_prime_id (id_of_mlid x) in
  let ids_renamed, env' = push_vars' [x', t] env in
  let x_renamed = fst (List.hd ids_renamed) in
  push_env_types [x_renamed, t];
  if x == Dummy then gen_stmts env' k b else
  let depth = tctx.current_letin_depth in
  tctx.current_letin_depth <- depth + 1;
  let use_unique = List.mem depth tctx.unique_bindings in
  (* Phase 2: set up dead-after info for move insertion.
     Compute free vars of the continuation [b] (shifted by 1 because [b] is
     under the let binder).  A variable at de Bruijn index [i] in [a] is
     dead-after if [i+1] is not free in [b] (since [b] has one extra binder).
     Only move if the variable has exactly 1 occurrence in [a]. *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let cont_free = Escape.free_rels 1 b in  (* free in b, shifted past let binder *)
  let dead_in_a = Escape.IntSet.filter (fun i ->
    (* i is dead after [a] if i is not free in [b] AND occurs exactly once in [a] *)
    not (Escape.IntSet.mem i cont_free) &&
    Escape.nb_occur_match i a = 1
  ) tctx.move_owned_vars in
  (* Also add any vars from our current dead set that have single occurrence in a *)
  let dead_from_above = Escape.IntSet.filter (fun i ->
    Escape.IntSet.mem i tctx.move_dead_after &&
    Escape.nb_occur_match i a = 1
  ) tctx.move_owned_vars in
  tctx.move_dead_after <- Escape.IntSet.union dead_in_a dead_from_above;
  let afun v = Sasgn (x_renamed, None, v) in
  let asgn = gen_stmts env afun a in
  tctx.move_dead_after <- saved_dead;
  (* The new let binding is owned (it's a local variable).
     Update move_owned_vars for processing [b]: shift all existing indices by 1
     (because [b] has one more binder) and add index 1 if the type is shared_ptr. *)
  let shifted_owned = Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars in
  let new_is_shared = Escape.is_shared_ptr_type t in
  let owned_for_b = if new_is_shared then Escape.IntSet.add 1 shifted_owned else shifted_owned in
  tctx.move_owned_vars <- owned_for_b;
  let tvars = get_current_type_vars () in
  let result = begin match asgn with
  | [ Sasgn (_, None, e) ] ->
    let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars t in
    let cpp_ty = if use_unique then shared_to_unique cpp_ty else cpp_ty in
    let e = if use_unique then shared_expr_to_unique e else e in
    Sasgn (x_renamed, Some cpp_ty, e) :: gen_stmts env' k b
  | _ ->
    let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars t in
    let cpp_ty = if use_unique then shared_to_unique cpp_ty else cpp_ty in
    Sdecl (x_renamed, cpp_ty) :: asgn @ gen_stmts env' k b
  end in
  tctx.move_owned_vars <- saved_owned;
  result
| MLapp (MLfix (x, ids, funs, _), args) ->
  (* Resolve unresolved metas in fix function types to Tvars using mgu.
     Traverse types and assign Tvar 1, 2, ... to each unresolved meta. *)
  let next_tvar = ref 1 in
  let rec resolve_metas = function
    | Miniml.Tmeta ({ contents = None } as m) ->
        let idx = !next_tvar in next_tvar := idx + 1;
        try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
    | Miniml.Tmeta { contents = Some t } -> resolve_metas t
    | Miniml.Tarr (t1, t2) -> resolve_metas t1; resolve_metas t2
    | Miniml.Tglob (_, args, _) -> List.iter resolve_metas args
    | _ -> () in
  Array.iter (fun (_, ty) -> resolve_metas ty) ids;
  Array.iter (resolve_metas_in_ast resolve_metas) funs;
  List.iter (resolve_metas_in_ast resolve_metas) args;
  (* Collect Tvars from bodies too *)
  let body_tvars = Array.fold_left collect_tvars_ast [] funs in
  let all_body_tvars = List.sort_uniq Int.compare body_tvars in
  (* Collect all Tvar indices from the fixpoint types *)
  let fix_tvar_indices = Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids in
  let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
  let outer_tvars = get_current_type_vars () in
  let n_outer = List.length outer_tvars in
  (* Check if fixpoint introduces Tvars beyond the outer scope *)
  let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
  if has_extra_tvars then begin
    (* Lift the polymorphic inner fixpoint to a top-level function *)
    let all_tvar_names = List.map (fun i ->
      if i <= n_outer then
        List.nth outer_tvars (i - 1)
      else
        Id.of_string ("T" ^ string_of_int i)
    ) fix_tvar_indices in
    let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
    let extended_tvar_names = build_extended_tvar_names fix_tvar_indices all_tvar_names all_body_tvars in
    let fix_name = fst (ids.(x)) in
    let outer_name = match tctx.current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
    (* Save and set current_type_vars to the extended tvar list for the lifted function.
       extended_tvar_names covers both signature and body Tvar indices. *)
    let saved_tvars = get_current_type_vars () in
    set_current_type_vars extended_tvar_names;
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled = Array.to_list (Array.mapi (fun i f ->
      gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f) funs) in
    set_current_type_vars saved_tvars;
    (* Build lifted declarations *)
    List.iteri (fun i ((renamed_id, fix_ty), params, body) ->
      let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty extended_tvar_names fix_ty in
      let (_, cod) = match cpp_ty with
        | Tfun (dom, cod) -> (dom, cod)
        | _ -> ([], cpp_ty) in
      let (cpp_params, all_temps_with_funs) =
        build_lifted_cpp_params (convert_ml_type_to_cpp_type env Refset'.empty extended_tvar_names) all_temps params in
      let rec_call = mk_cppglob lifted_ref (List.map (fun id -> Tvar (0, Some id)) all_tvar_names) in
      let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
      let inner = Dfundef ([lifted_ref, []], cod, cpp_params, body) in
      let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
      add_lifted_decl lifted_decl
    ) funs_compiled;
    (* Generate args in outer scope and call the lifted function.
       Build explicit type args: outer tvars stay as Tvar references, extra tvars
       are resolved to concrete types from the enclosing context.
       Extra tvars that appear as the fixpoint's return type are resolved to the
       enclosing function's C++ return type (current_cpp_return_type). *)
    let call_type_args =
      let extra_tvar_names = List.filter (fun id ->
        not (List.exists (Id.equal id) outer_tvars)) all_tvar_names in
      if extra_tvar_names = [] then
        (* All tvars are outer — C++ can deduce them *)
        []
      else begin
        (* Get the fixpoint's template return type to identify which extra tvar it uses *)
        let fix_ty = snd ids.(x) in
        let tmpl_cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty extended_tvar_names fix_ty in
        let tmpl_cod = match tmpl_cpp_ty with
          | Tfun (_, cod) -> cod | t -> t in
        let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
        let extra_args = List.map (fun tvar_name ->
          (* If this extra tvar IS the template return type, use the enclosing
             function's concrete return type as the instantiation. *)
          match tmpl_cod with
          | Tvar (_, Some id) when Id.equal id tvar_name ->
            (match tctx.current_cpp_return_type with
             | Some ret_ty -> ret_ty
             | None -> Tvar (0, Some tvar_name))
          | _ ->
            (* For non-return-type extra tvars, keep as Tvar — C++ may deduce them
               from arguments, or further analysis is needed. *)
            (match tctx.current_cpp_return_type with
             | Some ret_ty -> ret_ty  (* Best guess: use enclosing return type *)
             | None -> Tvar (0, Some tvar_name))
        ) extra_tvar_names in
        outer_args @ extra_args
      end
    in
    let cpp_args = List.rev_map (gen_expr env) args in
    [k (CPPfun_call (mk_cppglob lifted_ref call_type_args, cpp_args))]
  end else begin
    (* No extra Tvars - proceed with original local fixpoint approach *)
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled = Array.to_list (Array.mapi (fun i f ->
      gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f) funs) in
    let renamed_ids = List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled in
    let funs_with_params = List.map (fun (_, params, body) -> (params, body)) funs_compiled in
    let tvars = get_current_type_vars () in
    let fix_func_type ty =
      match ty with
      | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
          Minicpp.Tfun (params, Minicpp.Tvoid)
      | _ -> ty
    in
    let decls = List.map (fun (id, ty) ->
      Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env Refset'.empty tvars ty))) renamed_ids in
    let ret_ty ty = (match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
      | Tfun (_,t) ->
          (match t with
          | Minicpp.Tvar (_, None) -> None
          | _ -> Some t)
      | _ -> None) in
    let defs = List.map2 (fun (id, fty) (params, body) -> Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id) params, ret_ty fty, body, false))) renamed_ids funs_with_params in
    let args = List.rev_map (gen_expr env) args in
    decls @ defs @ [k (CPPfun_call (CPPvar (fst (List.nth renamed_ids x)), args))]
  end
| MLfix (x, ids, funs, _) ->
  (* Standalone fixpoint (not immediately applied) - e.g., in let binding *)
  (* Resolve unresolved metas in fix function types to Tvars using mgu. *)
  let next_tvar = ref 1 in
  let rec resolve_metas = function
    | Miniml.Tmeta ({ contents = None } as m) ->
        let idx = !next_tvar in next_tvar := idx + 1;
        try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
    | Miniml.Tmeta { contents = Some t } -> resolve_metas t
    | Miniml.Tarr (t1, t2) -> resolve_metas t1; resolve_metas t2
    | Miniml.Tglob (_, args, _) -> List.iter resolve_metas args
    | _ -> () in
  Array.iter (fun (_, ty) -> resolve_metas ty) ids;
  (* Call gen_fix with all mutual fixpoint names so each body can reference the others *)
  let all_fix_ids_list = Array.to_list ids in
  let funs_compiled = Array.to_list (Array.mapi (fun i f ->
    gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f) funs) in
  (* Extract the renamed ids from gen_fix results *)
  let renamed_ids = List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled in
  let funs_with_params = List.map (fun (_, params, body) -> (params, body)) funs_compiled in
  let tvars = get_current_type_vars () in
  (* For std::function declarations, if return type is an unnamed Tvar, use void as placeholder. *)
  let fix_func_type ty =
    match ty with
    | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
        Minicpp.Tfun (params, Minicpp.Tvoid)
    | _ -> ty
  in
  let decls = List.map (fun (id, ty) ->
    Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env Refset'.empty tvars ty))) renamed_ids in
  let ret_ty ty = (match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
    | Tfun (_,t) ->
        (match t with
        | Minicpp.Tvar (_, None) -> None
        | _ -> Some t)
    | _ -> None) in
  let defs = List.map2 (fun (id, fty) (params, body) -> Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id) params, ret_ty fty, body, false))) renamed_ids funs_with_params in
  (* Return the fix function itself (for use in let bindings etc.) *)
  decls @ defs @ [k (CPPvar (fst (List.nth renamed_ids x)))]
(* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
  gen_stmts env k (MLapp (a1, a2::[])) *)
| MLapp (MLglob (r, bind_tys), a1 :: a2 :: l) when is_bind r ->
  let (a, f) = Common.last_two (a1 :: a2 :: l) in
  let a = gen_expr env a in
  let ids',f = collect_lams f in
  (* Resolve metas in continuation parameter types using bind's type arguments.
     bind has type forall A B, IO A -> (A -> IO B) -> IO B.
     The first type argument is A, which is the type of the continuation parameter.
     Use mgu to unify them, which mutably resolves metas.
     Skip Tdummy entries in bind_tys — these come from failed type extractions
     in make_tyargs (e.g., HKT type constructors that can't be extracted).
     Unifying a meta with Tdummy would not resolve it usefully. *)
  let non_dummy_bind_tys = List.filter (fun t -> not (isTdummy t)) bind_tys in
  let () = match non_dummy_bind_tys with
    | elem_ty :: _ ->
        List.iter (fun (_, ty) -> try_mgu ty elem_ty) ids'
    | [] -> ()
  in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids') env in
  push_env_types ids;
  (match ids with
  | (x, ty) :: _ ->
    let tvars = get_current_type_vars () in
    let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ty in
    if ty == Tvoid || ty == Tunknown then
      Sexpr a :: gen_stmts env k f
    else
      Sasgn (x, Some ty, a) :: gen_stmts env k f
  | _ -> Sexpr a :: gen_stmts env k f)
| MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
  let t = Common.last (a1 :: l) in
  [k (gen_expr env t)]
| MLcase (typ, t, pv) when is_custom_match pv ->
    [gen_custom_cpp_case env k typ t pv]
| MLglob (r, _) when is_ghost r ->
  [Sreturn None]
| MLexn msg ->
  (* Generate throw statement for unreachable/absurd cases (e.g., empty match) *)
  [Sthrow msg]
| MLmagic (MLexn msg) ->
  (* Handle MLexn wrapped in MLmagic *)
  [Sthrow msg]
| t ->
  (* Tail position: all owned variables used here are at their last use.
     Set move_dead_after to include all owned variables that occur exactly once in t. *)
  let saved_dead = tctx.move_dead_after in
  let tail_dead = Escape.IntSet.filter (fun i ->
    Escape.nb_occur_match i t = 1
  ) tctx.move_owned_vars in
  tctx.move_dead_after <- Escape.IntSet.union tctx.move_dead_after tail_dead;
  let result = [k (gen_expr env t)] in
  tctx.move_dead_after <- saved_dead;
  result

and gen_fix env ?(all_fix_ids=[]) ~fix_idx (n,ty) f =
  let ids, f = collect_lams f in
  let ids,_ = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
  (* Push all mutual fixpoint names (or just (n,ty) for single fixpoints).
     For mutual fixpoints, all_fix_ids contains all fixpoint names in array order.
     For single fixpoints, all_fix_ids is empty and we use [(n,ty)]. *)
  let fix_names = if all_fix_ids = [] then [(n,ty)] else all_fix_ids in
  let n_fix_funs = List.length fix_names in
  let renamed_fix_ids, env = push_vars' (ids @ fix_names) env in
  let saved_env_types = tctx.env_types in
  push_env_types (ids @ fix_names);
  (* Extract the renamed name for THIS fixpoint function.
     fix_names are at the end of renamed_fix_ids, starting at position (List.length ids).
     For mutual fixpoints, fix_idx identifies which one is ours. *)
  let n_lam_params = List.length ids in
  let renamed_n = fst (List.nth renamed_fix_ids (n_lam_params + fix_idx)) in
  let ids = List.filter (fun (_,ty) -> not (ml_type_is_void ty)) ids in
  (* Phase 2: set up move state for fixpoint body.
     Fix params are owned (passed by value in the generated std::function lambda).
     After push_vars'(ids @ fix_names), de Bruijn indices in f are:
       ids[0] → db 1, ..., ids[k-1] → db k,
       fix_names[0] → db k+1, ..., fix_names[m-1] → db k+m.
     We only mark lambda params as owned (not the fix self-references). *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let n_fix_params = List.length ids in
  let fix_owned = Escape.infer_owned_params (n_fix_params + n_fix_funs) f in
  tctx.move_owned_vars <- List.fold_left (fun acc i ->
    let db = i + 1 in  (* ids[i] has db index i+1 *)
    let owned = match List.nth_opt fix_owned i with Some b -> b | None -> false in
    let ml_ty = snd (List.nth ids i) in
    if owned && Escape.is_shared_ptr_type ml_ty
    then Escape.IntSet.add db acc
    else acc
  ) Escape.IntSet.empty (List.init n_fix_params (fun i -> i));
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_n_params <- n_fix_params + n_fix_funs;
  let result = (renamed_n, ty), ids, gen_stmts env (fun x -> Sreturn (Some x)) f in
  tctx.env_types <- saved_env_types;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  result

(* TODO: REDO NAMESPACE AS PART OF NAMES!!! *)

let gen_ind_cpp vars name cnames tys =
  let constrdecl =
    Array.to_list (Array.mapi (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars x)) tys in
      let make_args = List.map(fun (x,_) -> mk_cppglob_local (GlobRef.VarRef x) []) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make = Dfundef ([c, []; GlobRef.VarRef (Id.of_string "make"), []], Tshared_ptr (Tglob (name, ty_vars, [])), List.rev constr,
        [Sreturn (Some (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)])))]) in
      (ty_vars == [], make))
    tys)
    |> List.filter_map (fun (keep, make) -> if keep then Some make else None)
  in
  Dnspace (Some name, constrdecl)

let gen_record_cpp name fields ind =
  let l = List.combine fields ind.ip_types.(0) in
  let l = List.mapi (fun i (x, t) ->
    let n = match x with
    | Some n -> n
    | None -> GlobRef.VarRef (Id.of_string ("_field" ^ (string_of_int i))) in
    (Fvar' (n, convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty ind.ip_vars t), VPublic)) l in
  let ty_vars = List.map (fun x -> (TTtypename, x)) ind.ip_vars in
  Dstruct { ds_ref = name; ds_fields = l; ds_tparams = ty_vars; ds_constraint = None }

(* Generate a C++ concept from a type class.
   Type class Eq(A) with method eqb : A -> A -> bool becomes:
   template<typename I, typename A>
   concept Eq = requires(A a0, A a1) {
     { I::eqb(a0, a1) } -> std::convertible_to<bool>;
   };

   Uses CPPconvertible_to with the actual cpp_type for the constraint,
   which will be pretty-printed in cpp.ml.
*)
let gen_typeclass_cpp name fields ind =
  let inst_id = Id.of_string "I" in
  (* Determine the number of non-promoted type variables (from ip_sign Keep entries).
     Promoted type variables (from erased Type fields) have Tvar indices beyond this. *)
  let nb_sign_keeps = List.length (List.filter (fun x -> x == Keep) ind.ip_sign) in
  (* Split ip_vars into param vars (real type params) and promoted vars (associated types) *)
  let param_vars = List.filteri (fun i _ -> i < nb_sign_keeps) ind.ip_vars in
  let promoted_vars = List.filteri (fun i _ -> i >= nb_sign_keeps) ind.ip_vars in
  (* Only param vars become concept template parameters; promoted vars become
     typename requirements inside the requires block *)
  let ty_vars = List.map (fun x -> (TTtypename, x)) param_vars in
  let all_params = (TTtypename, inst_id) :: ty_vars in
  (* Build typename requirements for promoted vars: typename I::field; *)
  let type_reqs = List.map (fun var_id ->
    Tqualified (Tvar (0, Some inst_id), var_id)
  ) promoted_vars in
  (* Substitute promoted Tvars with Tqualified(I, name) in cpp_type trees.
     After conversion, promoted vars appear as Tvar(_, Some name) where name
     is in promoted_vars. Replace them with typename I::name. *)
  let rec subst_promoted_in_cpp_type = function
    | Tvar (_, Some vname) when List.exists (Id.equal vname) promoted_vars ->
        Tqualified (Tvar (0, Some inst_id), vname)
    | Tfun (args, ret) ->
        Tfun (List.map subst_promoted_in_cpp_type args,
              subst_promoted_in_cpp_type ret)
    | Tglob (r, ts, es) ->
        Tglob (r, List.map subst_promoted_in_cpp_type ts, es)
    | Tshared_ptr t -> Tshared_ptr (subst_promoted_in_cpp_type t)
    | Tunique_ptr t -> Tunique_ptr (subst_promoted_in_cpp_type t)
    | Tnamespace (r, t) -> Tnamespace (r, subst_promoted_in_cpp_type t)
    | Tqualified (b, id) -> Tqualified (subst_promoted_in_cpp_type b, id)
    | Tref t -> Tref (subst_promoted_in_cpp_type t)
    | Tvariant ts -> Tvariant (List.map subst_promoted_in_cpp_type ts)
    | Tid (id, ts) -> Tid (id, List.map subst_promoted_in_cpp_type ts)
    | Tmod (m, t) -> Tmod (m, subst_promoted_in_cpp_type t)
    | t -> t
  in
  (* Generate requires clauses for each method.
     Filter out Tdummy entries from ip_types — these are erased fields
     (e.g., carrier : Type in a promoted dependent record) that don't
     appear in the fields list (select_fields already skips them). *)
  let non_dummy_types = List.filter (fun t ->
    not (Mlutil.isTdummy t)) ind.ip_types.(0) in
  if List.length fields <> List.length non_dummy_types then
    Feedback.msg_debug Pp.(str "gen_typeclass_cpp: fields=" ++ int (List.length fields) ++
      str " non_dummy_types=" ++ int (List.length non_dummy_types) ++
      str " ip_types.(0)=" ++ int (List.length ind.ip_types.(0)));
  let method_list = List.combine fields non_dummy_types in
  (* Check if a type is a bare promoted Tvar — a Tvar whose index is beyond
     the real type parameters. This indicates the field's type is entirely
     determined by a promoted associated type, so we can't decompose it into
     args and return type at concept time (the concrete type might be a function). *)
  let is_bare_promoted_tvar ty =
    match ty with
    | Miniml.Tvar n -> n > nb_sign_keeps
    | _ -> false
  in
  (* Generate a single method requirement.
     Returns either:
     - `Normal (params, (call, constraint))` for regular methods
     - `Disjunctive expr` for fields whose type is a bare promoted Tvar *)
  let gen_method_req (field_opt, field_ty) =
    match field_opt with
    | None -> None  (* Anonymous field, skip *)
    | Some field_ref ->
        let method_name = Common.pp_global_name Term field_ref in
        if is_bare_promoted_tvar field_ty then begin
          (* Field type is a bare promoted Tvar (e.g., fun_ind_prf : fun_ind_prf_ty).
             The concrete type could be a plain value or a function with any arity.
             Generate a disjunctive concept requirement:
               requires { { I::method() } -> std::convertible_to<T>; } ||
               requires { { I::method } -> std::convertible_to<T>; }
             The first clause handles nullary accessors (Meyers singleton pattern).
             The second handles functions (pointer converts to std::function) and
             static data members (direct value). *)
          let ret_cpp = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty ind.ip_vars field_ty in
          let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
          let constraint_expr = CPPconvertible_to ret_cpp in
          let qualified = CPPqualified (CPPvar inst_id, Id.of_string method_name) in
          let call_form = CPPrequires ([], [(CPPfun_call (qualified, []), constraint_expr)], []) in
          let value_form = CPPrequires ([], [(qualified, constraint_expr)], []) in
          Some (`Disjunctive (CPPbinop ("||", call_form, value_form)))
        end else begin
          let (args, ret) = get_args_and_ret [] field_ty in
          (* Filter out type class instance arguments (they're passed via template) *)
          let args = List.filter (fun t -> not (Table.is_typeclass_type t)) args in
          let ret_cpp = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty ind.ip_vars ret in
          let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
          (* Create parameter names: a0, a1, a2, ... *)
          let params = List.mapi (fun j arg_ty ->
            let arg_cpp = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty ind.ip_vars arg_ty in
            let arg_cpp = subst_promoted_in_cpp_type arg_cpp in
            (arg_cpp, Id.of_string ("a" ^ string_of_int j))
          ) args in
          (* Method call: I::method_name(a0, a1, ...) *)
          let call_args = List.map (fun (_, id) -> CPPvar id) params in
          let call = CPPfun_call (
            CPPqualified (CPPvar inst_id, Id.of_string method_name),
            call_args
          ) in
          (* Constraint: use the cpp_type directly - cpp.ml will render it *)
          let constraint_expr = CPPconvertible_to ret_cpp in
          Some (`Normal (params, (call, constraint_expr)))
        end
  in
  let all_reqs = List.filter_map (fun pair -> gen_method_req pair) method_list in
  (* Separate normal requirements from disjunctive ones *)
  let normal_reqs = List.filter_map (function `Normal r -> Some r | _ -> None) all_reqs in
  let disjunctive_exprs = List.filter_map (function `Disjunctive e -> Some e | _ -> None) all_reqs in
  (* Build the concept body.
     Normal requirements go in a single requires{} block.
     Disjunctive requirements (for bare-Tvar fields) are &&-ed separately,
     each wrapped in parentheses via the || rendering. *)
  let concept_body =
    let normal_part =
      if normal_reqs = [] then None
      else begin
        let all_params_flat = List.concat_map fst normal_reqs in
        let seen = ref [] in
        let dedup_params = List.filter (fun (_ty, id) ->
          let key = Id.to_string id in
          if List.mem key !seen then false
          else (seen := key :: !seen; true)
        ) all_params_flat in
        let constraints = List.map snd normal_reqs in
        Some (CPPrequires (dedup_params, constraints, type_reqs))
      end
    in
    match normal_part, disjunctive_exprs with
    | Some np, [] -> np
    | None, [d] ->
        if type_reqs <> [] then
          CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
        else d
    | None, d :: rest ->
        let base = if type_reqs <> [] then
          CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
        else d in
        List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) base rest
    | Some np, ds -> List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) np ds
    | None, [] ->
        if type_reqs <> [] then CPPrequires ([], [], type_reqs)
        else CPPrequires ([], [], [])  (* degenerate: no requirements *)
  in
  Dtemplate (all_params, None, Dconcept (name, concept_body))

(* Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct (name : GlobRef.t) (body : ml_ast) (ty : ml_type)
    : cpp_decl option * GlobRef.t option * ml_type list =
  (* For parameterized instances, strip Tarr/MLlam layers to get to the inner
     typeclass type and constructor body. Collect template parameters along the way.
     Example: numOption has type Tarr(Tdummy, Tarr(Tglob(Numeric,[A],[]), Tglob(Numeric,[option A],[])))
     and body MLlam(_, Tdummy, MLlam(_, Tglob(Numeric,...), MLcons(...))) *)
  let rec strip_outer_layers ty body tc_idx tc_acc lam_acc =
    match ty, body with
    | Tarr (arg_ty, rest_ty), MLlam (ml_id, lam_ty, rest_body) ->
        if Mlutil.isTdummy arg_ty then
          (* Erased type parameter — skip (template params are inferred from
             type variables in the return type via collect_ml_tvars below) *)
          strip_outer_layers rest_ty rest_body tc_idx
            tc_acc ((id_of_mlid ml_id, lam_ty) :: lam_acc)
        else if Table.is_typeclass_type arg_ty then begin
          (* Typeclass constraint — becomes a template typename for the instance *)
          let instance_name = Id.of_string ("_tcI" ^ string_of_int tc_idx) in
          strip_outer_layers rest_ty rest_body (tc_idx + 1)
            ((TTtypename, instance_name) :: tc_acc)
            ((instance_name, lam_ty) :: lam_acc)
        end else
          (* Not a type param or typeclass — stop stripping *)
          (ty, body, List.rev tc_acc, List.rev lam_acc)
    | _ -> (ty, body, List.rev tc_acc, List.rev lam_acc)
  in
  let (inner_ty, inner_body, tc_temps, lam_params) =
    strip_outer_layers ty body 0 [] [] in
  (* Collect type variables from the inner return type's type args.
     For parameterized instances like numOption : Numeric (option A),
     the return type is Tglob(Numeric, [option A], []) which contains Tvar for A.
     These need to become template typename parameters (T1, T2, etc.). *)
  let rec collect_ml_tvars acc = function
    | Miniml.Tvar i ->
        if List.mem i acc then acc
        else i :: acc
    | Miniml.Tarr (t1, t2) -> collect_ml_tvars (collect_ml_tvars acc t1) t2
    | Miniml.Tglob (_, tys, _) -> List.fold_left collect_ml_tvars acc tys
    | _ -> acc
  in
  let tv_temps = match inner_ty with
    | Tglob (_, type_args, _) ->
        let raw = List.fold_left collect_ml_tvars [] type_args in
        List.sort compare raw |> List.mapi (fun i _ ->
          (TTtypename, Id.of_string ("T" ^ string_of_int (i + 1))))
    | _ -> []
  in
  (* Template params: typeclass params first, then type vars (matches gen_dfun convention) *)
  let template_params = tc_temps @ tv_temps in
  (* Now inner_ty should be Tglob(class_ref, type_args, _) and inner_body should be MLcons(...) *)
  match inner_ty with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref ->
      (* Get the type class fields (method names) and field types (from ind_packet) *)
      let fields = Table.record_fields_of_type inner_ty in
      let field_types = List.filter (fun t ->
        not (Mlutil.isTdummy t)) (Table.record_field_types class_ref) in
      (* Strip MLmagic wrapper if present — promoted dependent records
         may have their constructor wrapped in MLmagic due to Tvar/Tglob
         mismatches during extraction unification. *)
      let inner_body = match inner_body with MLmagic b -> b | b -> b in
      (match inner_body with
      | MLcons (cons_ty, _ctor_ref, method_bodies) ->
          (* For promoted dependent records, the definition type Tglob(Magma,[],[])
             has no type_args, but the MLcons type Tglob(Magma,[nat],[]) carries
             the concrete types extracted from the erased constructor args. *)
          let type_args = match cons_ty with
            | Tglob (_, ta, _) when ta <> [] -> ta
            | _ -> type_args
          in
          (* Build the environment with lambda parameters for de Bruijn resolution.
             For parameterized instances, method bodies reference the outer lambda
             parameters (e.g., the typeclass dictionary) via MLrel indices.
             We push lam_params into the env so these references resolve correctly. *)
          let base_env = snd (push_vars' (List.rev lam_params) (empty_env ())) in
          (* Collect type var names for convert_ml_type_to_cpp_type *)
          let type_var_names = List.map snd tv_temps in
          (* Set up type variable context for fixpoint lifting.
             Without this, fixpoints inside methods get lifted with wrong names
             and missing template parameters. *)
          let saved_outer_name = tctx.current_outer_function_name in
          tctx.current_outer_function_name <- Some (Common.pp_global_name Term name);
          set_current_type_vars type_var_names;
          (* Generate static methods for each field *)
          let gen_method (field_ref, field_ml_ty) field_body =
            match field_ref with
            | None -> None  (* Anonymous field, skip *)
            | Some method_ref ->
                let method_name = Id.of_string (Common.pp_global_name Term method_ref) in
                (* Strip MLmagic wrappers from the field body — promoted dependent
                   records produce MLmagic due to Tvar/Tglob mismatches. *)
                let rec strip_magic = function
                  | MLmagic b -> strip_magic b
                  | b -> b
                in
                let field_body = strip_magic field_body in
                (* Substitute type class parameter with instance's type arg in the field type.
                   This gives us the concrete return type (e.g., bool for eqb: A -> A -> bool).
                   For promoted dependent records, type_args may be empty, leaving Tvars
                   unsubstituted — we handle that below by using lambda binder types. *)
                let subst_ty = Mlutil.type_subst_list type_args field_ml_ty in
                (* Extract parameter names and types from the lambda.
                   For promoted type vars (e.g., Tvar 3 for edge in Graph),
                   substitute them with their concrete types from type_args.
                   Only substitute Tvars beyond the ip_sign Keep count to
                   avoid disturbing regular type variable references. *)
                let nb_sign_keeps = List.length tv_temps in
                let subst_promoted_tvars ty =
                  if List.length type_args > nb_sign_keeps then
                    let rec subst = function
                      | Miniml.Tvar j when j > nb_sign_keeps && j <= List.length type_args ->
                          List.nth type_args (j - 1)
                      | Miniml.Tarr (a, b) -> Miniml.Tarr (subst a, subst b)
                      | Miniml.Tglob (r, l, a) -> Miniml.Tglob (r, List.map subst l, a)
                      | Miniml.Tmeta {contents = Some t} -> subst t
                      | Miniml.Tmeta _ as t -> t
                      | t -> t
                    in
                    subst ty
                  else ty
                in
                let rec extract_params ml_acc cpp_acc body =
                  match body with
                  | MLlam (id, ty, rest) ->
                      let param_name = id_of_mlid id in
                      let resolved_ty = subst_promoted_tvars ty in
                      let param_cpp_ty = convert_ml_type_to_cpp_type base_env Refset'.empty type_var_names resolved_ty in
                      extract_params ((param_name, resolved_ty) :: ml_acc) ((param_name, param_cpp_ty) :: cpp_acc) rest
                  | _ -> (List.rev ml_acc, List.rev cpp_acc, body)
                in
                let (ml_params, cpp_params, inner_body) = extract_params [] [] field_body in
                (* Determine return type: if type_subst resolved everything, use the
                   substituted type. Otherwise, infer from the lambda binders. *)
                let method_ret_ty =
                  let ret = ml_return_type subst_ty in
                  match ret with
                  | Tvar _ | Tvar' _ when ml_params <> [] ->
                      (* Unsubstituted Tvar — infer from the last lambda binder's type.
                         For op : A -> A -> A with body MLlam(x, nat, MLlam(y, nat, ...)),
                         the return type is the same as the parameter type (nat). *)
                      let last_param_ty = snd (List.hd (List.rev ml_params)) in
                      convert_ml_type_to_cpp_type base_env Refset'.empty type_var_names last_param_ty
                  | Tvar _ | Tvar' _ ->
                      (* No lambda binders to infer from — try to use the field type's
                         arg types. For a non-function field like m_id : carrier, the
                         whole type is Tvar, so look at the body's type. *)
                      Tany
                  | _ ->
                      convert_ml_type_to_cpp_type base_env Refset'.empty type_var_names ret
                in
                let (cpp_params, ret_ty, body_stmts) =
                  if ml_params = [] then begin
                    (* No lambdas in the body — either a function reference that
                       needs eta-expansion, or a non-function value field. *)
                    let (arg_types, _ret_type) = get_args_and_ret [] subst_ty in
                    (* Filter out type class instance args *)
                    let arg_types = List.filter (fun t -> not (Table.is_typeclass_type t)) arg_types in
                    if arg_types = [] then begin
                      (* Non-function field (like m_id : carrier) — generate as a
                         static value with a nullary accessor method. *)
                      let stmts = gen_stmts base_env (fun x -> Sreturn (Some x)) inner_body in
                      ([], method_ret_ty, stmts)
                    end else begin
                      (* Function reference — eta-expand based on the field type's args *)
                      let params = List.mapi (fun i arg_ty ->
                        let name = Id.of_string ("a" ^ string_of_int i) in
                        let cpp_ty = convert_ml_type_to_cpp_type base_env Refset'.empty type_var_names arg_ty in
                        (name, arg_ty, cpp_ty)
                      ) arg_types in
                      let nparams = List.length params in
                      let ml_rels = List.mapi (fun i _ -> MLrel (nparams - i)) params in
                      (* Lift the body's de Bruijn indices to account for the new eta params *)
                      let lifted_body = Mlutil.ast_lift nparams inner_body in
                      let call_expr = MLapp (lifted_body, ml_rels) in
                      let ml_vars = List.rev_map (fun (name, ml_ty, _) -> (name, ml_ty)) params in
                      let env = snd (push_vars' ml_vars base_env) in
                      let stmts = gen_stmts env (fun x -> Sreturn (Some x)) call_expr in
                      let cpp_params = List.map (fun (name, _, cpp_ty) -> (name, cpp_ty)) params in
                      (cpp_params, method_ret_ty, stmts)
                    end
                  end else begin
                    (* Normal case: we have lambdas *)
                    let env = snd (push_vars' (List.rev ml_params) base_env) in
                    let stmts = gen_stmts env (fun x -> Sreturn (Some x)) inner_body in
                    (cpp_params, method_ret_ty, stmts)
                  end
                in
                Some (Fmethod { mf_name = method_name; mf_tparams = []; mf_ret_type = ret_ty; mf_params = cpp_params; mf_body = body_stmts; mf_is_const = false; mf_is_static = true }, VPublic)
          in
          (* Zip fields with their types from ind_packet *)
          let fields_with_types =
            if List.length fields = List.length field_types then
              List.combine fields field_types
            else
              (* Fallback: pair fields with Tunknown if lengths don't match *)
              List.map (fun f -> (f, Miniml.Tunknown)) fields
          in
          if List.length fields_with_types <> List.length method_bodies then
            Feedback.msg_debug Pp.(str "gen_instance_struct: fields_with_types=" ++
              int (List.length fields_with_types) ++ str " method_bodies=" ++
              int (List.length method_bodies));
          let method_pairs = List.combine fields_with_types method_bodies in
          let methods = List.filter_map (fun ((fld, fty), body) -> gen_method (fld, fty) body) method_pairs in
          (* Restore type variable context *)
          tctx.current_outer_function_name <- saved_outer_name;
          clear_current_type_vars ();
          (* Compute promoted vars and generate using fields.
             Promoted vars are ip_vars entries beyond the real type parameter count
             (as determined by ip_sign Keep count, not tv_temps which reflects the
             instance's own type variables).
             They become `using field = ConcreteType;` in the struct. *)
          let ip_vars = Table.get_ind_ip_vars class_ref in
          let nb_sign_keeps_for_promoted = Table.get_ind_nb_sign_keeps class_ref in
          let promoted_vars = List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) ip_vars in
          let promoted_concrete_types =
            if List.length type_args > nb_sign_keeps_for_promoted then
              List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) type_args
            else []
          in
          let using_fields =
            if List.length promoted_vars = List.length promoted_concrete_types then
              List.map2 (fun var_name concrete_ml_ty ->
                let concrete_cpp_ty = convert_ml_type_to_cpp_type base_env Refset'.empty type_var_names concrete_ml_ty in
                (Fnested_using (var_name, concrete_cpp_ty), VPublic)
              ) promoted_vars promoted_concrete_types
            else []
          in
          (* Exclude promoted type args from the returned list (used for static_assert) *)
          let non_promoted_type_args =
            List.filteri (fun i _ -> i < nb_sign_keeps_for_promoted) type_args
          in
          if methods = [] && using_fields = [] then (None, Some class_ref, non_promoted_type_args)
          else begin
            let decl = Dstruct { ds_ref = name; ds_fields = using_fields @ methods;
                                 ds_tparams = template_params; ds_constraint = None } in
            (Some decl, Some class_ref, non_promoted_type_args)
          end
      | _ -> (None, Some class_ref, type_args))
  | _ -> (None, None, [])

(* Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (_body : ml_ast) (ty : ml_type) : bool =
  match ml_return_type ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(* Collect (index, name) pairs for all Tvar occurrences, sorted by index *)
let get_tvars_indexed t =
  let get_name i n =
    match n with
    | None -> Id.of_string ("T" ^ string_of_int i)
    | Some n -> n in
  let rec aux l = function
    | Tvar (i, n) -> if List.exists (fun (x, _) -> i == x) l
                  then l
                  else (i, get_name i n) :: l
    | Tglob (_, tys, _) -> List.fold_left aux l tys
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | Tunique_ptr ty -> aux l ty
    | _ -> l in
  List.sort (fun (x,_) (y,_) -> Int.compare x y) (aux [] t)

(* Tvar names, sorted by index *)
let get_tvars t =
  List.map snd (get_tvars_indexed t)

(* Tvar indices only (unsorted) *)
let get_tvar_indices t =
  List.map fst (get_tvars_indexed t)

(* Collect tvar indices that are deducible by the C++ compiler: those appearing
   in the codomain or in non-function-typed domain params.  Function-typed
   params are excluded because gen_dfun converts them to auto-deduced Fn&&
   template parameters, hiding their original Rocq-level type variables from
   C++ template argument deduction.  Used by both gen_dfun (to decide whether
   a function param should get a MapsTo constraint or plain TTtypename) and
   gen_decl_for_pp (to filter out phantom tvars from the template param list). *)
let primary_tvar_indices dom cod =
  let non_fun_dom = List.filter (fun t -> match t with Tfun _ -> false | _ -> true) dom in
  List.fold_left (fun acc t ->
    List.fold_left (fun a i -> IntSet.add i a) acc (get_tvar_indices t)
  ) IntSet.empty (cod :: non_fun_dom)


let rec glob_subst_expr (id : GlobRef.t) (e1 : cpp_expr) (e2 : cpp_expr) =
match e2 with
  | CPPglob (id', _, _) ->
    if Environ.QGlobRef.equal Environ.empty_env id id' then e1 else e2
  | CPPnamespace (id', e') -> CPPnamespace (id', glob_subst_expr id e1 e')
  | CPPfun_call (f, args) -> CPPfun_call (glob_subst_expr id e1 f, List.map (glob_subst_expr id e1) args)
  | CPPderef e' -> CPPderef (glob_subst_expr id e1 e')
  | CPPmove e' -> CPPmove (glob_subst_expr id e1 e')
  | CPPlambda (args, ty, b, cbv) -> CPPlambda (args, ty, List.map (glob_subst_stmt id e1) b, cbv)
  | CPPoverloaded cases -> CPPoverloaded (List.map (glob_subst_expr id e1) cases)
  | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map (glob_subst_expr id e1) args)
  | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map (glob_subst_expr id e1) args)
  | CPPget (e', id') -> CPPget (glob_subst_expr id e1 e', id')
  | CPPget' (e', id') -> CPPget' (glob_subst_expr id e1 e', id')
  | CPPparray (args, e') -> CPPparray (Array.map (glob_subst_expr id e1) args, glob_subst_expr id e1 e')
  | _ -> e2 (* lambda needs to be covered *)

and glob_subst_stmt (id : GlobRef.t) (e : cpp_expr) (s : cpp_stmt) =
match s with
  | Sreturn (Some e') -> Sreturn (Some (glob_subst_expr id e e'))
  | Sreturn None -> Sreturn None
  | Sasgn (id', ty, e') -> Sasgn (id', ty, glob_subst_expr id e e')
  | Sexpr e' -> Sexpr (glob_subst_expr id e e')
  | Scustom_case (ty, e', tys, brs, str) -> Scustom_case (ty, glob_subst_expr id e e', tys,
    List.map (fun (args, ty, stmts) -> (args, ty, List.map (glob_subst_stmt id e) stmts)) brs, str)
  | Sswitch (scrut, ind, brs) -> Sswitch (glob_subst_expr id e scrut, ind,
    List.map (fun (ctor, stmts) -> (ctor, List.map (glob_subst_stmt id e) stmts)) brs)
  | _ -> s

let rec var_subst_expr (id : Id.t) (e1 : cpp_expr) (e2 : cpp_expr) =
match e2 with
  | CPPvar id' -> if Id.equal id id' then e1 else e2
  | CPPnamespace (id', e') -> CPPnamespace (id', var_subst_expr id e1 e')
  | CPPfun_call (f, args) -> CPPfun_call (var_subst_expr id e1 f, List.map (var_subst_expr id e1) args)
  | CPPderef e' -> CPPderef (var_subst_expr id e1 e')
  | CPPmove e' -> CPPmove (var_subst_expr id e1 e')
  | CPPlambda (args, ty, b, cbv) -> CPPlambda (args, ty, List.map (var_subst_stmt id e1) b, cbv)
  | CPPoverloaded cases -> CPPoverloaded (List.map (var_subst_expr id e1) cases)
  | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map (var_subst_expr id e1) args)
  | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map (var_subst_expr id e1) args)
  | CPPget (e', id') -> CPPget (var_subst_expr id e1 e', id')
  | CPPget' (e', id') -> CPPget' (var_subst_expr id e1 e', id')
  | CPPparray (args, e') -> CPPparray (Array.map (var_subst_expr id e1) args, var_subst_expr id e1 e')
  | CPPmethod_call (obj, meth, args) -> CPPmethod_call (var_subst_expr id e1 obj, meth, List.map (var_subst_expr id e1) args)
  | CPPmember (e', mid) -> CPPmember (var_subst_expr id e1 e', mid)
  | CPParrow (e', mid) -> CPParrow (var_subst_expr id e1 e', mid)
  | CPPforward (ty, e') -> CPPforward (ty, var_subst_expr id e1 e')
  | CPPnew (ty, args) -> CPPnew (ty, List.map (var_subst_expr id e1) args)
  | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ty, var_subst_expr id e1 e')
  | CPPunique_ptr_ctor (ty, e) -> CPPunique_ptr_ctor (ty, var_subst_expr id e1 e)
  | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, tys, List.map (var_subst_expr id e1) args)
  | CPPqualified (e', qid) -> CPPqualified (var_subst_expr id e1 e', qid)
  | CPPbinop (op, lhs, rhs) -> CPPbinop (op, var_subst_expr id e1 lhs, var_subst_expr id e1 rhs)
  | _ -> e2

and var_subst_stmt (id : Id.t) (e : cpp_expr) (s : cpp_stmt) =
  let sub_e = var_subst_expr id e in
  let sub_s = var_subst_stmt id e in
  match s with
  | Sreturn (Some e') -> Sreturn (Some (sub_e e'))
  | Sreturn None -> Sreturn None
  | Sasgn (id', ty, e') -> Sasgn (id', ty, sub_e e')
  | Sexpr e' -> Sexpr (sub_e e')
  | Scustom_case (ty, e', tys, brs, str) -> Scustom_case (ty, sub_e e', tys,
    List.map (fun (args, ty, stmts) -> (args, ty, List.map sub_s stmts)) brs, str)
  | Sswitch (scrut, ind, brs) -> Sswitch (sub_e scrut, ind,
    List.map (fun (ctor, stmts) -> (ctor, List.map sub_s stmts)) brs)
  | Sif (cond, then_stmts, else_stmts) ->
      Sif (sub_e cond, List.map sub_s then_stmts, List.map sub_s else_stmts)
  | Sassign_field (obj, field, e') ->
      Sassign_field (sub_e obj, field, sub_e e')
  | _ -> s

(* Substitute unnamed type variables with named ones based on a variable list.
   This is used when generating methods to replace T1, T2, etc. with the struct's
   template parameter names like A, B, etc. *)
let rec tvar_subst_type (tvars : Id.t list) (ty : cpp_type) : cpp_type =
  match ty with
  | Tvar (i, None) ->
    (try Tvar (i, Some (List.nth tvars (pred i)))
     with Failure _ -> ty)
  | Tvar (_, Some _) -> ty  (* Already named *)
  | Tglob (r, tys, args) -> Tglob (r, List.map (tvar_subst_type tvars) tys, args)
  | Tfun (tys, ty) -> Tfun (List.map (tvar_subst_type tvars) tys, tvar_subst_type tvars ty)
  | Tmod (m, ty) -> Tmod (m, tvar_subst_type tvars ty)
  | Tnamespace (r, ty) -> Tnamespace (r, tvar_subst_type tvars ty)
  | Tref ty -> Tref (tvar_subst_type tvars ty)
  | Tvariant tys -> Tvariant (List.map (tvar_subst_type tvars) tys)
  | Tshared_ptr ty -> Tshared_ptr (tvar_subst_type tvars ty)
  | Tunique_ptr ty -> Tunique_ptr (tvar_subst_type tvars ty)
  | Tid (id, tys) -> Tid (id, List.map (tvar_subst_type tvars) tys)
  | Tqualified (ty, id) -> Tqualified (tvar_subst_type tvars ty, id)
  | _ -> ty  (* Tvoid, Ttodo, Tunknown *)

let rec tvar_subst_expr (tvars : Id.t list) (e : cpp_expr) : cpp_expr =
  let subst_ty = tvar_subst_type tvars in
  let subst_e = tvar_subst_expr tvars in
  match e with
  | CPPglob (r, tys, ci) -> CPPglob (r, List.map subst_ty tys, ci)
  | CPPnamespace (r, e') -> CPPnamespace (r, subst_e e')
  | CPPfun_call (f, args) -> CPPfun_call (subst_e f, List.map subst_e args)
  | CPPderef e' -> CPPderef (subst_e e')
  | CPPmove e' -> CPPmove (subst_e e')
  | CPPlambda (params, ret, body, cbv) ->
      let params' = List.map (fun (ty, id) -> (subst_ty ty, id)) params in
      let ret' = Option.map subst_ty ret in
      CPPlambda (params', ret', List.map (tvar_subst_stmt tvars) body, cbv)
  | CPPoverloaded cases -> CPPoverloaded (List.map subst_e cases)
  | CPPstructmk (r, tys, args) -> CPPstructmk (r, List.map subst_ty tys, List.map subst_e args)
  | CPPstruct (r, tys, args) -> CPPstruct (r, List.map subst_ty tys, List.map subst_e args)
  | CPPget (e', id) -> CPPget (subst_e e', id)
  | CPPget' (e', id) -> CPPget' (subst_e e', id)
  | CPPparray (args, e') -> CPPparray (Array.map subst_e args, subst_e e')
  | CPPmethod_call (obj, meth, args) -> CPPmethod_call (subst_e obj, meth, List.map subst_e args)
  | CPPmember (e', mid) -> CPPmember (subst_e e', mid)
  | CPParrow (e', mid) -> CPParrow (subst_e e', mid)
  | CPPforward (ty, e') -> CPPforward (subst_ty ty, subst_e e')
  | CPPnew (ty, args) -> CPPnew (subst_ty ty, List.map subst_e args)
  | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (subst_ty ty, subst_e e')
  | CPPunique_ptr_ctor (ty, e) -> CPPunique_ptr_ctor (subst_ty ty, subst_e e)
  | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, List.map subst_ty tys, List.map subst_e args)
  | CPPqualified (e', qid) -> CPPqualified (subst_e e', qid)
  | CPPmk_shared ty -> CPPmk_shared (subst_ty ty)
  | CPPmk_unique ty -> CPPmk_unique (subst_ty ty)
  | _ -> e  (* CPPvar, CPPvisit, CPPstring, CPPuint, CPPfloat, CPPthis, CPPrequires *)

and tvar_subst_stmt (tvars : Id.t list) (s : cpp_stmt) : cpp_stmt =
  let subst_ty = tvar_subst_type tvars in
  let subst_e = tvar_subst_expr tvars in
  let subst_s = tvar_subst_stmt tvars in
  match s with
  | Sreturn (Some e) -> Sreturn (Some (subst_e e))
  | Sreturn None -> Sreturn None
  | Sdecl (id, ty) -> Sdecl (id, subst_ty ty)
  | Sasgn (id, ty_opt, e) -> Sasgn (id, Option.map subst_ty ty_opt, subst_e e)
  | Sexpr e -> Sexpr (subst_e e)
  | Scustom_case (ty, e, tys, brs, str) ->
      Scustom_case (subst_ty ty, subst_e e, List.map subst_ty tys,
        List.map (fun (args, ty, stmts) ->
          (List.map (fun (id, ty) -> (id, subst_ty ty)) args, subst_ty ty, List.map subst_s stmts)) brs,
        str)
  | Sthrow msg -> Sthrow msg  (* throw statements don't need substitution *)
  | Sswitch (scrut, ind, brs) -> Sswitch (subst_e scrut, ind,
    List.map (fun (ctor, stmts) -> (ctor, List.map subst_s stmts)) brs)
  | Sassert _ as s -> s  (* raw strings don't need type var substitution *)
  | Sif (cond, then_stmts, else_stmts) ->
      Sif (subst_e cond, List.map subst_s then_stmts, List.map subst_s else_stmts)
  | Sraw _ as s -> s
  | Sassign_field (obj, field, e) ->
      Sassign_field (subst_e obj, field, subst_e e)

(** Detect function-typed parameter positions that receive a freshly
    constructed lambda in a self-recursive call.

    Higher-order function parameters are normally emitted as C++ template
    parameters constrained with a [MapsTo] concept:

      template <MapsTo<T1, unsigned int> F0,
                MapsTo<T1, shared_ptr<tree>, T1, shared_ptr<tree>, T1> F1>
      static T1 tree_rect(F0 &&f, F1 &&f0, const shared_ptr<tree> &t);

    This is preferred because template parameters preserve the exact lambda
    type, enabling the compiler to inline the call — there is no
    type-erasure overhead as there would be with [std::function].

    However, this breaks when a self-recursive function passes a *new*
    lambda at a function-typed parameter position in its own recursive
    call.  This is the continuation-passing style (CPS) pattern:

      template <MapsTo<unsigned int, unsigned int> F1>
      static unsigned int fact_cps(unsigned int n, F1 &&k) {
        ...
        return fact_cps(n_, [&](unsigned int r) { return k(n_ * r); });
      }

    Each recursive call wraps [k] inside a fresh lambda with a unique
    type.  Because [F1] is a template parameter, the compiler must
    instantiate a new specialization of [fact_cps] for every nesting
    depth.  That creates an infinite chain of template instantiations
    and the compiler rejects the program.

    The fix is to emit those specific parameters as [std::function]
    instead.  [std::function] is a concrete type — the continuation's
    type is always [std::function<unsigned int(unsigned int)>] regardless
    of how many lambdas are wrapped around it, so the recursive call
    resolves to the same function and no new instantiation is needed:

      static unsigned int fact_cps(
          unsigned int n,
          const std::function<unsigned int(unsigned int)> k) {
        ...
        return fact_cps(n_, [&](unsigned int r) { return k(n_ * r); });
      }

    Only parameters that actually exhibit this pattern are affected.
    For example, in [partition_cps p l k], the predicate [p] is passed
    unchanged to the recursive call ([partition_cps p rest (fun ...)]),
    so [p] stays as a template parameter while [k] becomes
    [std::function].  Similarly, non-recursive higher-order functions
    like [tree_rect] never trigger this issue and keep full template
    parameters throughout.

    The detection works by walking the function body's ML AST, looking
    for self-recursive calls [MLapp(MLglob(self_ref, _), args)].  For
    each such call, we check which argument positions contain a lambda
    ([MLlam]).  Those positions are the CPS parameters that must use
    [std::function]. *)
let detect_cps_params (self_ref : GlobRef.t) (n_params : int) (body : ml_ast) : int list =
  let cps_set = Hashtbl.create 4 in
  let rec walk = function
    | MLapp (MLglob (r, _), args) when Environ.QGlobRef.equal Environ.empty_env r self_ref ->
      List.iteri (fun i arg ->
        if i < n_params && contains_lambda arg then
          Hashtbl.replace cps_set i true) args
    | MLapp (f, args) -> walk f; List.iter walk args
    | MLlam (_, _, body) -> walk body
    | MLletin (_, _, e1, e2) -> walk e1; walk e2
    | MLcase (_, scrut, branches) ->
      walk scrut;
      Array.iter (fun (_, _, _, body) -> walk body) branches
    | MLcons (_, _, args) -> List.iter walk args
    | MLtuple args -> List.iter walk args
    | MLfix (_, _, bodies, _) -> Array.iter walk bodies
    | MLmagic e -> walk e
    | MLparray (elts, def) -> Array.iter walk elts; walk def
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> ()
  and contains_lambda = function
    | MLlam _ -> true
    | MLletin (_, _, _, body) -> contains_lambda body
    | MLmagic e -> contains_lambda e
    | _ -> false
  in
  walk body;
  Hashtbl.fold (fun k _ acc -> k :: acc) cps_set []

(* TODO: CLEANUP: dom and cod are redundant with ty *)
let gen_dfun n b dom cod ty temps =
  let ids,b = collect_lams b in
  let rec get_dom l ty = match ty with
    | Tarr (t1, t2) -> get_dom (t1 :: l) t2
    | _ -> l in
  let mldom = get_dom [] ty in
  (* get_missing computes the types for eta-expansion parameters.
     mldom contains domain types in reversed order (innermost type first).
     ids contains explicit lambdas in reversed order (innermost lambda first).

     The explicit lambdas bind the OUTERMOST types (at the END of mldom).
     The missing parameters should have the INNERMOST types (at the START of mldom).

     Example: For type R -> nat -> nat -> nat with body λr. <match>:
       mldom = [nat; nat; R]  (innermost nat is first, outermost R is last)
       ids = [(r, R)]         (one lambda binding the outermost type R)
       missing types = [nat; nat]  (the first 2 elements of mldom)

     The old code consumed from HEAD of both lists, incorrectly pairing
     the innermost type (nat) with the outermost lambda (r), causing
     eta-expansion parameters to get wrong types. *)
  let get_missing d a =
    let n_missing = max 0 (List.length d - List.length a) in
    List.firstn n_missing d in
  let missing_types = get_missing mldom ids in
  let n_miss = List.length missing_types in
  (* Assign names so that _x0 gets the outermost missing type (closest to the
     explicit lambdas) and _x(n-1) gets the innermost (= last source param).
     get_missing returns types innermost-first from mldom, so index i maps to
     name _x(n_miss - 1 - i).  The resulting list is already in de Bruijn order
     (innermost first) because mapi iterates innermost-first. *)
  let missing = List.mapi (fun i t -> (Id (Id.of_string ("_x" ^ string_of_int (n_miss - 1 - i))), t)) missing_types in
  (* Unify body lambda parameter types with the function signature types.

     When optimize_fix (mlutil.ml) promotes a polymorphic let-fix into a
     top-level Dfix, the body's lambda parameter types may still contain
     unresolved Tmeta cells left over from extraction.  For example:

       Definition local_length {A} (l : list A) : nat :=
         let fix go (xs : list A) := ... in go l.

     After optimize_fix, the outer function IS the fixpoint, but the lambda
     parameter type for [xs] still holds the original unresolved meta for A,
     while the function's signature type [ty] correctly has Tvar 1 for A.
     Without unification, convert_ml_type_to_cpp_type maps the unresolved
     meta to Tany (std::any), producing e.g. list<std::any> instead of
     list<T1>.

     By unifying each body parameter type with the corresponding signature
     type via try_mgu, we resolve the shared Tmeta cells in-place.  Because
     metas are mutable references shared across the entire body AST, this
     single unification step also fixes every other occurrence of the same
     meta inside the function body (match annotations, recursive calls, etc.). *)
  let n_missing = List.length missing in
  let sig_types_for_ids = List.of_seq (Seq.drop n_missing (List.to_seq mldom)) in
  let rec unify_param_types body_params sig_types = match body_params, sig_types with
    | (id, body_ty) :: rest_params, sig_ty :: rest_sig ->
      (try try_mgu body_ty sig_ty with _ -> ());
      (id, body_ty) :: unify_param_types rest_params rest_sig
    | _ -> body_params in
  let ids = unify_param_types ids sig_types_for_ids in
  (* Replace Tunknown in body param types with corresponding sig types.
     This handles promoted dependent records where the lambda's type annotation
     has Tunknown for the erased carrier, while the function signature has
     Tglob(m_carrier, []) which can be resolved by convert_ml_type_to_cpp_type. *)
  let rec merge_unknown body_ty sig_ty =
    match body_ty, sig_ty with
    | Miniml.Tunknown, _ -> sig_ty
    | Miniml.Tglob (r1, ts1, a1), Miniml.Tglob (r2, ts2, _)
      when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
        Miniml.Tglob (r1, List.map2 merge_unknown ts1 ts2, a1)
    | Miniml.Tarr (t1a, t1b), Miniml.Tarr (t2a, t2b) ->
        Miniml.Tarr (merge_unknown t1a t2a, merge_unknown t1b t2b)
    | _ -> body_ty
  in
  let ids = if List.length ids = List.length sig_types_for_ids then
    List.map2 (fun (id, body_ty) sig_ty ->
      (id, merge_unknown body_ty sig_ty)
    ) ids sig_types_for_ids
  else ids in
  (* Detect which function-typed parameters are CPS parameters (see
     [detect_cps_params] above for the full explanation).  These are
     excluded from template-parameter promotion below — they keep their
     [Tmod(TMconst, Tfun(dom, cod))] type which prints as
     [const std::function<R(Args...)>].

     [detect_cps_params] returns source-order indices (param 0 = first
     Rocq parameter).  We need two index-checking helpers because the
     parameter list [ids] is in de Bruijn order (innermost first = last
     source param first), while [List.rev ids] is in source order:

       Source order (Rocq):      p0  p1  p2       indices 0, 1, 2
       De Bruijn order (ids):    p2  p1  p0       indices 0, 1, 2

     So CPS source index [i] maps to de Bruijn index [n_ids - 1 - i]. *)
  let cps_param_indices = detect_cps_params n (List.length ids) b in
  let cps_set = IntSet.of_list cps_param_indices in
  let is_cps_param_source i = IntSet.mem i cps_set in
  let n_ids = List.length ids in
  let is_cps_param_db i = IntSet.mem (n_ids - 1 - i) cps_set in
  let all_params = missing @ ids in
  (* Type class instance parameters become C++ template type parameters.
     We assign unique names (_tcI0, _tcI1, ...) to avoid collision with:
     - User variable names like 'i', 'j', etc.
     - Other generated names in the same scope
     The original parameter order is preserved for correct de Bruijn indexing. *)
  let typeclass_counter = ref 0 in
  let typeclass_temps = ref [] in
  let all_params_for_env = List.map (fun (ml_id, ty) ->
    if Table.is_typeclass_type ty then begin
      let i = !typeclass_counter in
      typeclass_counter := i + 1;
      let instance_name = Id.of_string ("_tcI" ^ string_of_int i) in
      (* Build template param info *)
      let temp_info = match ty with
        | Miniml.Tglob (class_ref, type_args, _) ->
            let type_arg_cpp = List.map (fun t -> convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] t) type_args in
            (TTtypename, instance_name, Some (class_ref, type_arg_cpp), remove_prime_id (id_of_mlid ml_id))
        | _ -> (TTtypename, instance_name, None, remove_prime_id (id_of_mlid ml_id))
      in
      typeclass_temps := temp_info :: !typeclass_temps;
      (* Return renamed param for env (use instance_name like 'i' instead of original name) *)
      (instance_name, ty)
    end else
      (* Regular param: keep original name *)
      (remove_prime_id (id_of_mlid ml_id), ty)
  ) all_params in
  let typeclass_temps = List.rev !typeclass_temps in
  (* Push params into environment for de Bruijn lookup during body generation.
     collect_lams returns params in reverse order (innermost first), so MLrel 1
     refers to the last param in the list.

     push_vars' may rename parameters to avoid collisions. For example, if Rocq has:
       fun (f : T) (f0 : F) (f : forest) => ...
     push_vars' renames the duplicate 'f' to 'f1', producing: [f; f0; f1]

     We must use these renamed ids (all_ids) for both:
     1. The environment (for correct de Bruijn lookup in the body)
     2. The C++ function signature (so parameter names match body references)

     Previously, the code discarded all_ids and used original names for the signature,
     causing mismatches like: void foo(T f, F f0, forest f) { ... f1->v() ... }
     where 'f1' in the body didn't match any parameter name. *)
  let all_ids, env = push_vars' all_params_for_env (empty_env ()) in
  reset_env_types ();
  push_env_types all_ids;
  (* Infer owned/borrowed for each parameter.
     all_params has n elements in de Bruijn order (element 0 = de Bruijn 1 = innermost).
     infer_owned_params returns a bool list in the same order. *)
  let n_params = List.length all_params in
  let owned_flags = Escape.infer_owned_params n_params b in
  (* Zip all_ids with ownership flags.  all_ids and all_params have the same length
     (push_vars' preserves length), so owned_flags aligns 1:1. *)
  let all_ids_with_owned = List.map2 (fun (id, ty) owned -> (id, ty, owned)) all_ids owned_flags in
  (* For function signature, use renamed ids but exclude typeclass and void params *)
  let ids_with_owned = List.filter (fun (_, ty, _) ->
    not (Table.is_typeclass_type ty) && not (ml_type_is_void ty)) all_ids_with_owned in
  (* Convert ML types to C++ types and wrap with const.
     Owned shared_ptr params: pass by value (shared_ptr<T>)
     Borrowed shared_ptr params: pass by const ref (const shared_ptr<T>&) *)
  let ids = List.map (fun (x, ty, owned) ->
    let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty [] ty in
    let wrapped = match cpp_ty with
      | Tshared_ptr _ when owned -> cpp_ty  (* shared_ptr<T> by value — owned *)
      | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, cpp_ty))  (* const shared_ptr<T>& — borrowed *)
      | _ -> Tmod (TMconst, cpp_ty)  (* const T *)
    in
    (x, wrapped)) ids_with_owned in
  (* Promote non-CPS function-typed parameters to C++ template parameters.

     Function-typed parameters (those with C++ type [Tmod(TMconst, Tfun(...))])
     are normally promoted to template parameters with [MapsTo] concept
     constraints.  This replaces [const std::function<R(Args...)>] with a
     template type variable [F&&], giving the compiler the exact lambda
     type so it can inline the call body — no type-erasure overhead.

     For example, [tree_rect]'s two function parameters become:

       template <MapsTo<T1, unsigned int> F0,
                 MapsTo<T1, shared_ptr<tree>, T1, shared_ptr<tree>, T1> F1>
       static T1 tree_rect(F0 &&f, F1 &&f0, ...);

     This works for [tree_rect] because its recursive calls pass [f] and
     [f0] unchanged — the template type stays the same at every recursion
     depth.

     CPS parameters are excluded from this promotion.  A CPS parameter
     receives a *new* lambda at each recursive call site, which means the
     template type would be different at each recursion depth, causing
     infinite template instantiation.  These parameters keep their
     [const std::function<R(Args...)>] type, which is a concrete
     (non-template) type that stays the same regardless of lambda wrapping.

     For example, [partition_cps p l k] has three parameters:
     - [p] is passed unchanged to the recursive call → template [F0 &&p]
     - [l] is not function-typed → stays as-is
     - [k] receives a new lambda at the recursive call → [const std::function<...> k]

     This loop iterates [List.rev ids] which is in source order,
     so we use [is_cps_param_source] for the CPS guard. *)
  (* Determine which tvars are "primary" — deducible from non-function domain
     params or the return type.  Function-typed params that reference tvars
     outside this set (e.g., erased HKT type variables) get TTtypename (no
     MapsTo constraint) instead of TTfun, to avoid referencing template type
     parameters that were filtered out as phantom by gen_decl_for_pp.
     Similarly, function-typed params containing HKT erasure markers (Tany
     or dummy_type) also get TTtypename, since their type structure has been
     partially erased and a MapsTo constraint would be malformed. *)
  let primary = primary_tvar_indices dom cod in
  let fun_tys = List.filter_map (fun (x, ty, i) ->
      match ty with
      |  (Tmod (TMconst, Tfun (fdom, fcod))) when not (is_cps_param_source i) ->
        let fun_idx = get_tvar_indices (Tfun (fdom, fcod)) in
        let has_undeclared = List.exists (fun idx -> not (IntSet.mem idx primary)) fun_idx in
        if has_undeclared || has_hkt_erasure (Tfun (fdom, fcod)) then
          Some (x, TTtypename, Id.of_string ("F" ^ (string_of_int i)))
        else
          Some (x, TTfun (fdom, fcod), Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids)) in
  (* Replace the parameter type of promoted (non-CPS) function params with
     the template type variable [F&&].  CPS params are left untouched — they
     keep [Tmod(TMconst, Tfun(dom, cod))] which prints as
     [const std::function<R(Args...)>].
     This loop iterates [ids] which is in de Bruijn order,
     so we use [is_cps_param_db] for the CPS guard. *)
  let ids = List.mapi (fun i (x, ty) ->
      match ty with
      |  (Tmod (TMconst, Tfun (dom, cod))) when not (is_cps_param_db i) ->
        (x, Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ (string_of_int ((List.length ids) - i - 1))))))))
      | _ -> (x, ty)) ids in
  (* TODO: below is needed for lambdas in recursive positions, but is badddddd. *)
  (* let rec_fun_tys = List.map (fun (_,t, _) ->
    match t with
    | TTfun (dom, cod) -> Tref (Tmod (TMconst, Tfun (dom, cod)))
    | _ -> assert false) fun_tys in
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps @ rec_fun_tys) in *)
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic = List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps in
  (* Build recursive call reference with typeclass and type params only.
     Function type params (from fun_tys) are excluded because they should be
     deduced from arguments, not explicitly specified in recursive calls. *)
  let rec_call_temps = typeclass_temps_basic @ temps in
  let rec_call = mk_cppglob n (List.map (fun (_, id) -> Tvar (0, Some id)) rec_call_temps) in
  (* Combine all template params for function signature.
     Save the non-typeclass type params for Tvar index resolution below. *)
  let regular_temps = temps @ (List.map (fun (_,t,n) -> (t,n)) fun_tys) in
  let temps = typeclass_temps_basic @ regular_temps in
  (* TODO: Build requires clause for type class constraints
     For now, type class constraints are not enforced at compile time.
     The constraints would use the typeclass_temps info to generate
     requires clauses like: requires Eq<I, T1> *)
  (* let forward_fun_args stmt = List.fold_left (fun s (x, _, fid) ->
    var_subst_stmt x (CPPforward (Tvar (0, Some fid), CPPvar x)) s) stmt fun_tys in *)
  (* Set current type variables for pattern matching lambda generation.
     These are the template parameters that can be used in type annotations.
     Exclude typeclass instance params — they are not ML type variables
     and should not participate in Tvar index resolution. ML Tvar indices
     (Tvar 1, Tvar 2, ...) correspond to regular type params only. *)
  let type_var_ids = List.filter_map (fun (tt, id) ->
    match tt with TTtypename | TTtypename_default _ -> Some id | _ -> None) regular_temps in
  set_current_type_vars type_var_ids;
  set_current_param_types all_ids;
  (* Set the outer function name so inner fixpoints can generate lifted names *)
  let saved_outer_name = tctx.current_outer_function_name in
  tctx.current_outer_function_name <- Some (Common.pp_global_name Term n);
  (* Check if the return type is coinductive - if so, wrap body in lazy thunk *)
  let ml_ret = ml_return_type ty in
  let is_cofix_return = Table.is_coinductive_type ml_ret in
  (* For cofixpoints, wrap the return expression in Type::ctor::lazy_([=]() -> ret_ty { ... }) *)
  let cofix_wrap x =
    if is_cofix_return then
      let ret_cpp = cod in
      let coind_ref = match ml_ret with
        | Miniml.Tglob (r, _, _) -> r
        | _ -> assert false in
      let type_args = match ml_ret with
        | Miniml.Tglob (_, args, _) ->
          List.map (fun t -> convert_ml_type_to_cpp_type env Refset'.empty type_var_ids t) args
        | _ -> [] in
      let lazy_factory = CPPqualified (
        CPPqualified (mk_cppglob coind_ref type_args, Id.of_string "ctor"),
        Id.of_string "lazy_") in
      let thunk = CPPlambda ([], Some ret_cpp,
        [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
    else
      Sreturn (Some x) in
  (* Generate sigma type precondition assertions *)
  let sigma_asserts =
    let assertions = Table.get_sigma_assertions n in
    if assertions = [] then []
    else
      let all_id_arr = Array.of_list (List.rev all_ids) in  (* outermost param first *)
      (* Substitute %0, %1, ... placeholders with actual parameter names *)
      let subst_placeholders template =
        let result = ref template in
        Array.iteri (fun i (id, _) ->
          let placeholder = Printf.sprintf "%%%d" i in
          let replacement = Id.to_string id in
          let buf = Buffer.create (String.length !result) in
          let s = !result in
          let len = String.length s in
          let plen = String.length placeholder in
          let j = ref 0 in
          while !j < len do
            if !j <= len - plen && String.sub s !j plen = placeholder then begin
              Buffer.add_string buf replacement;
              j := !j + plen
            end else begin
              Buffer.add_char buf s.[!j];
              j := !j + 1
            end
          done;
          result := Buffer.contents buf
        ) all_id_arr;
        !result
      in
      List.filter_map (fun (param_idx, assertion) ->
        if param_idx >= Array.length all_id_arr then None
        else
          match assertion with
          | Table.AssertExpr template ->
            let expr_str = subst_placeholders template in
            Some (Sassert (expr_str, Some expr_str))
          | Table.AssertComment comment ->
            Some (Sassert ("true", Some comment))
      ) assertions
  in
  tctx.unique_bindings <- Escape.analyze b;
  tctx.current_letin_depth <- 0;
  (* Phase 2: Initialize owned-variable tracking for move insertion.
     Parameters at de Bruijn indices 1..n_params; owned ones get added to the set. *)
  let n_all_params = List.length all_params in
  tctx.move_n_params <- n_all_params;
  tctx.move_owned_vars <- List.fold_left (fun acc (i, owned) ->
    if owned && Escape.is_shared_ptr_type (snd (List.nth all_params i))
    then Escape.IntSet.add (i + 1) acc
    else acc
  ) Escape.IntSet.empty (List.mapi (fun i o -> (i, o)) owned_flags);
  tctx.move_dead_after <- Escape.IntSet.empty;
  (* Expose the C++ return type to inner call sites so they can recover
     erased template type args (see try_recover_erased_return_type). *)
  let saved_return_type = tctx.current_cpp_return_type in
  tctx.current_cpp_return_type <- Some cod;
  let inner =
    if missing == [] then
      let b = List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b) in
      (* let b = List.map forward_fun_args b in *)
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfundef ([n, []], cod, ids, sigma_asserts @ b)
    else
      (* Eta-expansion: the body 'b' references original params starting at MLrel 1.
         After adding k=|missing| new params to the environment, the original params
         are now at indices k+1, k+2, etc. We must lift 'b' by k to adjust its references.

         Example: For accessor f : R -> nat -> nat -> nat with body λr. match r...
           - Original body references r as MLrel 1
           - After adding 2 eta-params (_x0, _x1), environment is [_x1; _x0; r]
           - r is now at index 3, so we lift b by 2: MLrel 1 -> MLrel 3

         Then we apply the lifted body to the eta-expansion arguments.

         Exception: axiom/exn bodies always throw — applying them to arguments
         produces invalid C++ (calling a void result). Generate the body directly. *)
      let b = match b with
        | MLaxiom _ | MLexn _ ->
          List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b)
        | _ ->
          let k = List.length missing in
          let lifted_b = ast_lift k b in
          let args = List.rev (List.mapi (fun i _ -> MLrel (i + 1)) missing) in
          List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap (MLapp (lifted_b, args)))
      in
      (* let b = List.map forward_fun_args b in *)
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfundef ([n, []], cod, ids, sigma_asserts @ b) in
  tctx.current_cpp_return_type <- saved_return_type;
  tctx.current_outer_function_name <- saved_outer_name;
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

(* TODO: is this used? Likely, but the template stuff shouldn't be. *)
let gen_sfun n b dom cod temps =
  let all_params, b = collect_lams b in
  let n_params = List.length all_params in
  let owned_flags = Escape.infer_owned_params n_params b in
  let ids, env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) all_params) (empty_env ()) in
  (* Zip with ownership flags, then filter out void params *)
  let ids_with_owned = List.map2 (fun (x, ty) owned -> (x, ty, owned)) ids owned_flags in
  let ids_with_owned = List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) ids_with_owned in
  (* Convert ML types to C++ types and wrap with const.
     Owned shared_ptr params: pass by value; Borrowed: const ref *)
  let ids = List.map (fun (x, ty, owned) ->
    let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty [] ty in
    let wrapped = match cpp_ty with
      | Tshared_ptr _ when owned -> cpp_ty  (* shared_ptr<T> by value — owned *)
      | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, cpp_ty))  (* const std::shared_ptr<T>& *)
      | _ -> Tmod (TMconst, cpp_ty)  (* const T *)
    in
    (Some x, wrapped)) ids_with_owned in
  let dom = List.filter (fun ty -> ty != Tvoid) dom in
  (* For already-converted C++ types in dom, wrap shared_ptr with const ref *)
  let args = List.mapi (fun i ty ->
    let wrapped = match ty with
      | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, ty))  (* const std::shared_ptr<T>& *)
      | _ -> Tmod (TMconst, ty)  (* const T *)
    in
    (None, wrapped)) dom in
  let inner = if List.length args > List.length ids (* TODO: find/fix bug so we don't need this *)
    then Dfundecl ([n, []], cod, List.rev args)
    else Dfundecl ([n, []], cod, ids) in
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

(* Build a map from erased field projection GlobRefs to their Tvar index
   for a promoted dependent record / typeclass.
   Returns [(GlobRef.t * int) list] where int is the 1-based Tvar index. *)
let erased_proj_tvar_map (class_ref : GlobRef.t) : (GlobRef.t * int) list =
  let open GlobRef in
  match class_ref with
  | IndRef (kn, _) | ConstructRef ((kn, _), _) ->
      let promoted_vars = Table.get_ind_ip_vars class_ref in
      if promoted_vars = [] then []
      else
        let mp = MutInd.modpath kn in
        let n_promoted = List.length promoted_vars in
        List.mapi (fun i var_id ->
          let knp = Constant.make2 mp (Label.of_id var_id) in
          (ConstRef knp, n_promoted - i)
        ) promoted_vars
  | _ -> []

(* Replace Tglob references to erased projections with Tvar' in an ML type. *)
let rec replace_erased_proj_refs (proj_map : (GlobRef.t * int) list) (t : ml_type) : ml_type =
  let find_in_map r =
    List.find_map (fun (ref, idx) ->
      if GlobRef.CanOrd.equal r ref then Some idx else None
    ) proj_map in
  match t with
  | Miniml.Tglob (r, ts, args) ->
      (match find_in_map r with
       | Some idx -> Miniml.Tvar' idx
       | None ->
           let ts' = List.map (replace_erased_proj_refs proj_map) ts in
           if ts == ts' then t else Miniml.Tglob (r, ts', args))
  | Miniml.Tarr (t1, t2) ->
      let t1' = replace_erased_proj_refs proj_map t1 in
      let t2' = replace_erased_proj_refs proj_map t2 in
      if t1 == t1' && t2 == t2' then t else Miniml.Tarr (t1', t2')
  | Miniml.Tunknown -> Miniml.Tvar' 1
  | _ -> t

(* Replace Tunknown in all type annotations within an ML AST body with the
   GlobRef of the first promoted type var (the carrier). This allows
   convert_ml_type_to_cpp_type to detect it as a promoted type var.
   [carrier_refs] is a list of (GlobRef.t * int) from erased_proj_tvar_map. *)
let rec rewrite_ml_ast_types (carrier_refs : (GlobRef.t * int) list) (ast : ml_ast) : ml_ast =
  if carrier_refs = [] then ast
  else
    let carrier_ref = fst (List.hd carrier_refs) in
    let rec rty t = match t with
      | Miniml.Tunknown -> Miniml.Tglob (carrier_ref, [], [])
      | Miniml.Tmeta ({contents = Some inner} as meta) ->
          let inner' = rty inner in
          if inner != inner' then meta.contents <- Some inner';
          t
      | Miniml.Tmeta ({contents = None} as meta) ->
          (* Unresolved meta — resolve to carrier *)
          meta.contents <- Some (Miniml.Tglob (carrier_ref, [], []));
          t
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (rty t1, rty t2)
      | Miniml.Tglob (r, ts, a) ->
          let ts' = List.map rty ts in
          Miniml.Tglob (r, ts', a)
      | _ -> t
    in
    let rast = rewrite_ml_ast_types carrier_refs in
    match ast with
    | MLlam (id, ty, body) ->
        MLlam (id, rty ty, rast body)
    | MLletin (id, ty, e1, e2) ->
        MLletin (id, rty ty, rast e1, rast e2)
    | MLglob (r, tys) ->
        MLglob (r, List.map rty tys)
    | MLcons (ty, r, args) ->
        MLcons (rty ty, r, List.map rast args)
    | MLtuple es ->
        MLtuple (List.map rast es)
    | MLcase (ty, scrut, branches) ->
        let branches' = Array.map (fun (binds, bty, pat, body) ->
          let binds' = List.map (fun (id, t) -> (id, rty t)) binds in
          (binds', rty bty, pat, rast body)
        ) branches in
        MLcase (rty ty, rast scrut, branches')
    | MLfix (i, name_types, bodies, is_cofix) ->
        let name_types' = Array.map (fun (id, ty) -> (id, rty ty)) name_types in
        let bodies' = Array.map rast bodies in
        MLfix (i, name_types', bodies', is_cofix)
    | MLapp (f, args) ->
        MLapp (rast f, List.map rast args)
    | MLmagic e ->
        MLmagic (rast e)
    | MLrel _ | MLdummy _ | MLaxiom _ | MLexn _ | MLuint _ | MLfloat _
    | MLparray _ | MLstring _ -> ast

(* Rewrite projection types for promoted dependent records.
   When a function's first parameter is a promoted typeclass (e.g., Magma),
   and the remaining args/return have erased carrier refs, replace
   them with Tvar references from the typeclass's field types.

   The function name [n] is used to find which field of the typeclass this
   projection corresponds to. *)
let rewrite_typeclass_projection_type (n : GlobRef.t) (ty : ml_type) : ml_type =
  match ty with
  | Tarr (Tglob (class_ref, _, _) as tc_arg, rest)
    when Table.is_typeclass class_ref ->
      let fields = Table.get_record_fields class_ref in
      let field_types = Table.record_field_types class_ref in
      let proj_map = erased_proj_tvar_map class_ref in
      if proj_map <> [] then
        (* Check if n is a projection of this typeclass *)
        let non_dummy_types = List.filter (fun t -> not (Mlutil.isTdummy t)) field_types in
        let non_dummy_fields_types =
          if List.length fields = List.length non_dummy_types then
            List.combine fields non_dummy_types
          else
            List.map (fun f -> (f, Miniml.Tunknown)) fields
        in
        let proj_name = Common.pp_global_name Term n in
        let matching_field_type = List.find_map (fun (field_ref_opt, ft) ->
          match field_ref_opt with
          | Some fr when Common.pp_global_name Term fr = proj_name -> Some ft
          | _ -> None
        ) non_dummy_fields_types in
        (match matching_field_type with
         | Some field_ty ->
             Tarr (tc_arg, field_ty)
         | None ->
             Tarr (tc_arg, replace_erased_proj_refs proj_map rest))
      else ty
  | _ -> ty

(* Get the erased projection map for a function's type, if it takes a
   promoted typeclass as first argument. *)
let get_erased_proj_map_from_type (ty : ml_type) : (GlobRef.t * int) list =
  match ty with
  | Tarr (Tglob (class_ref, _, _), _) when Table.is_typeclass class_ref ->
      erased_proj_tvar_map class_ref
  | _ -> []

let gen_decl n b ty =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) -> let (f, env) = gen_dfun n b dom cod ty temps in f , env , tvars
  | _ ->
    let inner = Dasgn (n, cty,  gen_expr (empty_env ()) b) in
    (match temps with
      | [] -> inner, empty_env () , tvars
      | l -> Dtemplate (l, None, inner), empty_env () , tvars)

let gen_decl_for_pp n b ty =
  let carrier_refs = get_erased_proj_map_from_type ty in
  let b = rewrite_ml_ast_types carrier_refs b in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  (* Filter out HKT-phantom tvars: tvars that appear ONLY in function-typed
     domain params that contain erased HKT types (Tany or dummy_type from
     Tdummy Ktype).  These cannot be deduced by the C++ compiler and must not
     appear as template parameters.

     Background: gen_dfun converts every function-typed param (e.g., f : A -> B)
     into an auto-deduced forwarding parameter (e.g., F1 &&f).  This means the
     original Rocq-level type variables that appear ONLY inside such function
     params (like A and B in hk_map's f : A -> B) are hidden from C++ template
     argument deduction — they don't appear anywhere in the generated C++
     signature.  We call these "phantom" tvars.

     primary_tvar_indices collects tvars from the codomain and non-function-typed
     domain params — positions where C++ CAN deduce the type.  We intentionally
     do NOT add tvars from clean (non-erased) function params, because those are
     also rendered as auto-deduced Fn params by gen_dfun.

     The fallback (erased_fun_dom = []) handles functions with no HKT erasure at
     all (e.g., compose): when there are no erased function params, all tvars
     are kept unconditionally, ensuring MapsTo constraints can reference them. *)
  let tvars = match cty with
    | Tfun (dom, cod) ->
      let tvars_indexed = get_tvars_indexed cty in
      let primary = primary_tvar_indices dom cod in
      let fun_dom = List.filter (fun t -> match t with Tfun _ -> true | _ -> false) dom in
      let erased_fun_dom = List.filter has_hkt_erasure fun_dom in
      (* Keep tvars that appear in primary (deducible) positions.
         If there are no erased function params at all, keep everything — this
         handles ordinary polymorphic functions that have no HKT erasure. *)
      List.filter_map (fun (i, id) ->
        if IntSet.mem i primary then Some id
        else if erased_fun_dom = [] then Some id
        else None
      ) tvars_indexed
    | _ -> tvars in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers use the full Dtemplate definition. *)
  let tc_param_ids = match ty with
    | Tarr _ ->
      let rec collect_tc_ids acc i = function
        | Miniml.Tarr (t1, t2) ->
          if Table.is_typeclass_type t1 then
            collect_tc_ids (Id.of_string ("_tcI" ^ string_of_int i) :: acc) (i+1) t2
          else
            collect_tc_ids acc i t2
        | _ -> List.rev acc
      in
      collect_tc_ids [] 0 ty
    | _ -> []
  in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) ->
    let f, e = gen_dfun n b dom cod ty temps in
  let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
  let tvars = tc_param_ids @ tvars @ fun_tys in
    Some f, e, tvars
  | _ ->
    None, empty_env (), (tc_param_ids @ tvars) (*
    let inner = Dasgn (n, Tmod (TMconst, ty),  gen_expr (empty_env ()) b) in
    (match temps with
      | [] -> inner, empty_env ()
      | l -> Dtemplate (l, inner), empty_env ())*)

(* TODO: maybe cleanup this function/its name etc.. *)
let gen_decl_for_dfuns n b ty =
  (* Simplify the ML type to resolve metavariables before converting to C++ *)
  let ty = type_simpl ty in
  (* Rewrite Tunknown in body types to promoted carrier refs.
     This allows convert_ml_type_to_cpp_type to resolve them correctly. *)
  let carrier_refs = get_erased_proj_map_from_type ty in
  let b = rewrite_ml_ast_types carrier_refs b in
  let b = resolve_body_tvars b ty in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers (gen_dfuns_header) use the full Dtemplate definition. *)
  let tc_param_ids = match ty with
    | Tarr _ ->
      let rec collect_tc_ids acc i = function
        | Miniml.Tarr (t1, t2) ->
          if Table.is_typeclass_type t1 then
            collect_tc_ids (Id.of_string ("_tcI" ^ string_of_int i) :: acc) (i+1) t2
          else
            collect_tc_ids acc i t2
        | _ -> List.rev acc
      in
      collect_tc_ids [] 0 ty
    | _ -> []
  in
  match cty with
  | Tfun (dom, cod) ->
    let (f, env) = gen_dfun n b dom cod ty temps in
    let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
    let tvars = tc_param_ids @ tvars @ fun_tys in
    f , env , tvars
  | _ -> let (f, env) = gen_dfun n b [Tvoid] cty ty temps in f , env , (tc_param_ids @ tvars)

let gen_spec n b ty =
  let ty = type_simpl ty in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match ty with
  | Tfun (dom, cod) -> gen_sfun n b dom cod temps
  | _ ->
    let b = gen_expr (empty_env ()) b in
    let inner = Dasgn (n, Tmod (TMconst, ty), b) in
    (match temps with
      | [] -> inner, empty_env ()
      | l -> Dtemplate (l, None, inner), empty_env ())

(* TODO: maybe cleanup this function/its name etc.. *)
let gen_spec_for_sfuns n b ty =
  let ty = type_simpl ty in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match ty with
  | Tfun (dom, cod) -> gen_sfun n b dom cod temps
  | _ -> gen_sfun n b [Tvoid] ty temps

let gen_dfuns (ns,bs,tys) =
  List.concat_map (fun (i, name) ->
    let result = gen_decl_for_dfuns name bs.(i) tys.(i) in
    (* Discard lifted declarations here - they are template functions that
       belong only in the header file (.h), not the source file (.cpp).
       gen_dfuns_header will collect them for the header. *)
    ignore (take_lifted_decls ());
    [result]
  ) (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(* Convert a Dfundef (definition with body) to a Dfundecl (declaration without body).
   Recursively handles Dtemplate wrappers. Used to generate forward declarations
   that match the full definition's signature (including concept constraints). *)
let rec decl_to_spec (d : cpp_decl) : cpp_decl =
  match d with
  | Dfundef (ids, ret_ty, params, _body) ->
    Dfundecl (ids, ret_ty, List.map (fun (id, ty) -> (Some id, ty)) params)
  | Dtemplate (temps, cstr, inner) ->
    Dtemplate (temps, cstr, decl_to_spec inner)
  | _ -> d  (* Already a declaration, return as-is *)

let gen_dfuns_header (ns,bs,tys) =
  List.concat_map (fun (i, name) ->
    let (ds, env, tvars) = gen_decl_for_dfuns name bs.(i) tys.(i) in
    let lifted = take_lifted_decls () in
    let lifted_results = List.map (fun d -> (d, empty_env ())) lifted in
    (* For non-template functions, derive the spec from the definition via
       decl_to_spec to ensure parameter types (owned vs borrowed) match exactly
       between the forward declaration and the out-of-line definition.
       Previously used gen_spec_for_sfuns which ran independent escape analysis
       and could produce different ownership decisions. *)
    let main_result = match tvars with
      | [] -> (decl_to_spec ds, env)
      | _::_ -> ds, env in
    lifted_results @ [main_result]
  ) (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(* Generate forward declarations (specs) for a group of mutually recursive functions,
   using the SAME signature as the full definitions. This ensures the specs match
   the out-of-line definitions (including concept-constrained template parameters).
   Unlike gen_dfuns_header which may use gen_spec_for_sfuns (producing simpler signatures),
   this always derives the spec from gen_decl_for_dfuns. *)
let gen_dfuns_spec (ns,bs,tys) =
  List.concat_map (fun (i, name) ->
    let (ds, _env, _tvars) = gen_decl_for_dfuns name bs.(i) tys.(i) in
    ignore (take_lifted_decls ());
    [(decl_to_spec ds, empty_env ())]
  ) (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(* Generate both spec and def for a group of mutually recursive functions in one pass.
   Calls gen_decl_for_dfuns ONCE per function, then derives:
   - spec: decl_to_spec of the full definition (forward declaration)
   - def: the full definition (for templates) or None (for non-templates in header mode)
   Returns list of (spec, def_option, lifted_decls) *)
let gen_dfuns_dual ~is_header (ns,bs,tys) =
  List.concat_map (fun (i, name) ->
    let (ds, env, tvars) = gen_decl_for_dfuns name bs.(i) tys.(i) in
    let lifted = take_lifted_decls () in
    let spec = (decl_to_spec ds, env) in
    let def = match tvars, is_header with
      | _::_, true -> Some (ds, env)   (* Template + header: full def in .h *)
      | _::_, false -> None            (* Template + source: already in .h *)
      | [], true -> None               (* Non-template + header: def goes in .cpp *)
      | [], false -> Some (ds, env)    (* Non-template + source: full def in .cpp *)
    in
    [(spec, def, lifted)]
  ) (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(* Generate both spec and def for a single Dterm function in one pass.
   Calls gen_decl_for_pp ONCE, then derives both spec and def.
   Returns (spec_opt, def_opt, tvars) *)
let gen_decl_for_pp_dual ~is_header n b ty =
  let (ds_opt, env, tvars) = gen_decl_for_pp n b ty in
  match ds_opt, tvars with
  | Some ds, _::_ ->
    (* Template function: spec is decl_to_spec, def only in header *)
    let def = if is_header then Some (ds, env) else None in
    (Some (decl_to_spec ds, env), def, tvars)
  | Some ds, [] ->
    (* Non-template function: spec via decl_to_spec to ensure parameter types
       (owned vs borrowed) match exactly between declaration and definition.
       Using gen_spec here would run independent escape analysis that may
       produce different ownership decisions than gen_dfun used for the def. *)
    let def = if is_header then None else Some (ds, env) in
    (Some (decl_to_spec ds, env), def, tvars)
  | None, _ ->
    (* Non-function type: no def needed *)
    let (spec_ds, spec_env) = gen_spec n b ty in
    (Some (spec_ds, spec_env), None, tvars)

let gen_ind_header vars name cnames tys =
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let add_templates d = match templates with
  | [] -> d
  | _ -> Dtemplate (templates, None, d) in
  let header = Array.to_list (Array.map (fun x -> add_templates (Dstruct_decl x)) cnames) in
  let vartydecl = add_templates (Dusing (name , Tvariant (Array.to_list (Array.map (fun x -> Tglob (x, List.mapi (fun i id -> Tvar (i, Some id)) vars, [])) cnames)))) in
  let constrdecl = Array.to_list (Array.mapi
    (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars x)) tys in
      (* For function parameters, use const ref for shared_ptr types *)
      let constr_params = List.map (fun (x, ty) ->
        let wrapped = match ty with
          | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, ty))  (* const std::shared_ptr<T>& *)
          | _ -> ty
        in
        (x, wrapped)) constr in
      let make_args = List.map(fun (x,_) -> mk_cppglob_local (GlobRef.VarRef x) []) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make_decl = Ffundecl (Id.of_string "make", Tmod (TMstatic, (ind_ty_ptr name ty_vars)), List.rev constr_params) in
      let make_def = Ffundef (Id.of_string "make", Tmod (TMstatic, Tshared_ptr (Tglob (name, ty_vars, []))), constr_params,
        [Sreturn (Some (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)])))]) in
      let fields = if ty_vars == []
        then List.append (List.map (fun (x, y) -> (Fvar (x,y), VPublic)) constr) [make_decl,VPublic]
        else List.append (List.map (fun (x, y) -> (Fvar (x,y), VPublic)) constr) [make_def,VPublic] in
      Dstruct { ds_ref = c; ds_fields = fields; ds_tparams = templates; ds_constraint = None })
    tys) in
  Dnspace (Some name, List.append (List.append header [vartydecl]) constrdecl)

(* Generate a single method from a method candidate.
   name: the containing type's GlobRef
   vars: type variables of the containing type
   (func_ref, body, ty, this_pos): the method candidate *)
let gen_single_method name vars (func_ref, body, ty, this_pos) =
  let num_ind_vars = List.length vars in
  let func_name = Id.of_string (Common.pp_global_name Term func_ref) in

  (* Get return type *)
  let (all_args, ret_ty) = get_args_and_ret [] ty in

  (* Determine the mapping from function type variables to inductive type variables.
     For same-module methods, the function uses Tvars 1..num_ind_vars for the inductive.
     For cross-module methods, the function may use different Tvar positions.
     We extract the actual mapping from the Tglob at this_pos.

     Example: fold_left has type (A → B → A) → list B → A → A
     where A=Tvar1 (accumulator), B=Tvar2 (list element).
     list<B> uses Tvar2, so ind_tvar_map = [(2, 1)] meaning "Tvar2 → ind var position 1".
     Then Tvar1 is "extra" and becomes template param T1. *)
  let ind_tvar_map =
    match List.nth_opt all_args this_pos with
    | Some (Miniml.Tglob (_, tvar_args, _)) ->
      (* Extract Tvar indices from the Tglob args, paired with their position *)
      List.concat (List.mapi (fun pos t ->
        match t with
        | Miniml.Tvar i | Miniml.Tvar' i -> [(i, pos + 1)]
        | _ -> []
      ) tvar_args)
    | _ ->
      (* Fallback for non-template types: assume positions 1..num_ind_vars *)
      List.init num_ind_vars (fun i -> (i + 1, i + 1))
  in
  let ind_tvar_set = IntSet.of_list (List.map fst ind_tvar_map) in
  (* Remap ML type variables: assign canonical positions so convert_ml_type_to_cpp_type
     maps them correctly.
     - Inductive tvars → positions 1..num_ind_vars
     - Extra tvars → positions num_ind_vars+1, num_ind_vars+2, ...
     This avoids collisions when the function uses different numbering than the inductive.

     Example: fold_left has Tvar1 (accum), Tvar2 (list elem)
       ind_tvar_map = [(2, 1)] — Tvar2 is the list element → position 1
       extra tvars: [1] — Tvar1 is extra → position 2 (= num_ind_vars + 1)
       Full remap: Tvar1 → 2, Tvar2 → 1 *)
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let extra_tvars_orig = List.filter (fun i -> not (IntSet.mem i ind_tvar_set)) all_tvars in
  let needs_remap = not (List.for_all (fun (src, dst) -> src = dst) ind_tvar_map)
                    || extra_tvars_orig <> [] in
  (* Build complete remap table: (original_idx → canonical_idx) *)
  let extra_remap = List.mapi (fun i orig -> (orig, num_ind_vars + 1 + i)) extra_tvars_orig in
  let full_remap = ind_tvar_map @ extra_remap in
  let remap_ml_tvar i =
    match List.assoc_opt i full_remap with
    | Some canonical -> canonical
    | None -> i
  in
  let rec remap_ml_type = function
    | Miniml.Tvar i -> Miniml.Tvar (remap_ml_tvar i)
    | Miniml.Tvar' i -> Miniml.Tvar' (remap_ml_tvar i)
    | Miniml.Tarr (t1, t2) -> Miniml.Tarr (remap_ml_type t1, remap_ml_type t2)
    | Miniml.Tglob (r, args, e) -> Miniml.Tglob (r, List.map remap_ml_type args, e)
    | Miniml.Tmeta { contents = Some t } -> remap_ml_type t
    | t -> t
  in
  let _ty = if needs_remap then remap_ml_type ty else ty in
  let ret_ty = if needs_remap then remap_ml_type ret_ty else ret_ty in
  let body = if needs_remap then Mlutil.remap_tvars remap_ml_tvar body else body in
  (* After remapping, extra tvars are at positions num_ind_vars+1, num_ind_vars+2, ... *)
  let extra_tvars = List.map snd extra_remap in
  let extra_tvar_names = List.mapi (fun i _ ->
    Id.of_string ("T" ^ string_of_int (i + 1))
  ) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars num_ind_vars extra_tvar_map in

  (* Convert return type *)
  let ret_cpp = convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars ret_ty in
  let ret_cpp = subst_extra_tvars ret_cpp in

  (* Collect lambda parameters and build environment for de Bruijn lookup.
     push_vars' may rename duplicate parameters (e.g., two params named 't' become 't', 't0').

     We must use the renamed ids (all_ids) consistently for:
     1. The environment - so gen_expr/gen_stmts produce correct variable references
     2. The C++ method signature - so parameter names match what the body references

     Previously, renamed ids were discarded and original names used for the signature,
     causing errors like: void method(tree t) { ... t0->v() ... }
     where 't0' in the body didn't exist as a parameter. *)
  let ids_with_types, inner_body = Mlutil.collect_lams body in
  let ids_converted = List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids_with_types in
  let all_ids, env = push_vars' ids_converted (empty_env ()) in
  reset_env_types ();
  push_env_types all_ids;
  (* Infer owned/borrowed for method parameters.
     Note: method 'this' is always borrowed (const method). *)
  let n_method_params = List.length ids_with_types in
  let method_owned_flags = Escape.infer_owned_params n_method_params inner_body in

  (* Extract 'this' argument at this_pos - use renamed ids for consistency with body *)
  let ids_normal_order = List.rev all_ids in
  let (this_arg_id_opt, param_ids_with_pos) = Common.extract_at_pos this_pos
    (List.mapi (fun i (id, ty) -> (id, ty, i)) ids_normal_order) in
  let this_arg_id = Option.map (fun (id, _, _) -> id) this_arg_id_opt in
  let param_ids_with_pos = List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) param_ids_with_pos in

  (* Build owned flag lookup for non-this params.
     ids_normal_order is outermost-first. de Bruijn index of element i in normal order
     = n_method_params - i.  method_owned_flags[db - 1] gives the owned flag. *)
  let get_param_owned_flag normal_order_idx =
    let db = n_method_params - normal_order_idx in
    match List.nth_opt method_owned_flags (db - 1) with
    | Some b -> b
    | None -> false
  in

  (* Convert params to C++ types *)
  let params_with_idx = List.mapi (fun i (id, ty, orig_idx) ->
    let cpp_ty = convert_ml_type_to_cpp_type env (Refset'.add name Refset'.empty) vars ty in
    let cpp_ty = subst_extra_tvars cpp_ty in
    let owned = get_param_owned_flag orig_idx in
    (id, cpp_ty, i, owned)
  ) param_ids_with_pos in

  (* Extract function-typed parameters for template params *)
  let fun_params = List.filter_map (fun (id, cpp_ty, i, _) ->
    match cpp_ty with
    | Tfun (dom, cod) -> Some (id, TTfun (dom, cod), Id.of_string ("F" ^ string_of_int i))
    | _ -> None
  ) params_with_idx in

  (* Build template params *)
  let extra_type_params = List.map (fun name -> (TTtypename, name)) extra_tvar_names in
  let fun_template_params = List.map (fun (_, tt, fname) -> (tt, fname)) fun_params in
  let template_params = extra_type_params @ fun_template_params in

  (* Build final params with proper wrapping.
     Use escape analysis to determine owned vs borrowed: owned params are passed by value
     (for move semantics), borrowed params are passed by const ref.
     This matches gen_dfun's logic to ensure forward declarations and definitions agree. *)
  let params = List.map (fun (id, cpp_ty, i, owned) ->
    let wrapped = match cpp_ty with
      | Tfun _ -> Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ string_of_int i)))))
      | Tshared_ptr _ | Tunique_ptr _ ->
        if owned then cpp_ty  (* Pass by value for owned params *)
        else Tref (Tmod (TMconst, cpp_ty))  (* Const ref for borrowed params *)
      | _ -> Tmod (TMconst, cpp_ty)
    in
    (id, wrapped)
  ) params_with_idx in

  (* For coinductive return types, wrap return in lazy thunk *)
  let is_cofix_method = Table.is_coinductive_type ret_ty in
  let method_k x =
    if is_cofix_method then
      let type_args = match ret_ty with
        | Miniml.Tglob (_, args, _) ->
          List.map (fun t -> convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars t) args
        | _ -> [] in
      let coind_ref = match ret_ty with
        | Miniml.Tglob (r, _, _) -> r
        | _ -> assert false in
      let lazy_factory = CPPqualified (
        CPPqualified (mk_cppglob coind_ref type_args, Id.of_string "ctor"),
        Id.of_string "lazy_") in
      let thunk = CPPlambda ([], Some ret_cpp,
        [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
    else
      Sreturn (Some x) in
  (* Generate method body.
     Save and reset move state: methods have const this, so all params are borrowed.
     No reuse optimization possible since 'this' is a raw pointer in methods. *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let saved_type_vars = get_current_type_vars () in
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_owned_vars <- Escape.IntSet.empty;
  tctx.move_n_params <- 0;
  tctx.unique_bindings <- Escape.analyze inner_body;
  tctx.current_letin_depth <- 0;
  (* Set current type vars to include both the inductive's type vars and extra tvars.
     This ensures gen_expr/eta_fun correctly convert Tvars to named C++ types
     when processing the method body (e.g., recursive calls carry type args). *)
  set_current_type_vars (vars @ extra_tvar_names);
  let stmts = gen_stmts env method_k inner_body in
  set_current_type_vars saved_type_vars;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  (* Add type args to recursive self-calls.
     Inside fixpoint bodies, the extraction produces MLglob(func_ref, []) with
     empty type args for recursive references. When the function is a method,
     the recursive call needs explicit template args for non-deducible params.
     Replace CPPglob(func_ref, []) with CPPglob(func_ref, all_type_args).

     The type args must be in the ORIGINAL tys order (matching ind_tvar_positions
     used by pp_cpp_expr for filtering). Position i in tys corresponds to Tvar (i+1)
     in the original ML type. After remapping, Tvar (i+1) → remap_ml_tvar(i+1).
     We construct the C++ type arg from extended_vars at that remapped position. *)
  let extended_vars = vars @ extra_tvar_names in
  let all_method_type_args =
    List.map (fun orig_tvar_idx ->
      let remapped = remap_ml_tvar orig_tvar_idx in
      let name = List.nth extended_vars (remapped - 1) in
      Tvar (remapped - 1, Some name)
    ) all_tvars
  in
  let stmts = if all_method_type_args <> [] then
    let self_call_with_tys = mk_cppglob func_ref all_method_type_args in
    List.map (glob_subst_stmt func_ref self_call_with_tys) stmts
  else stmts in
  let stmts = match this_arg_id with
    | Some id -> List.map (var_subst_stmt id CPPthis) stmts
    | None -> stmts
  in
  (* Apply tvar_subst_stmt with the extended vars list (defined above).
     extended_vars covers positions 1..num_ind_vars (inductive vars) and
     num_ind_vars+1, num_ind_vars+2, etc. (extra vars) so tvar_subst_stmt
     can name them all correctly. *)
  let stmts = List.map (tvar_subst_stmt extended_vars) stmts in

  (Fmethod { mf_name = func_name; mf_tparams = template_params; mf_ret_type = ret_cpp; mf_params = params; mf_body = stmts; mf_is_const = true; mf_is_static = false }, VPublic)

(* New inductive generation: encapsulated struct with methods *)
(* Generates:
   struct Tree {
     struct Leaf {};
     struct Node { std::shared_ptr<Tree> left; std::shared_ptr<Tree> right; };
     using variant_t = std::variant<Leaf, Node>;
   private:
     variant_t v_;
     explicit Tree(Leaf x) : v_(x) {}
     explicit Tree(Node x) : v_(std::move(x)) {}
   public:
     struct ctor {
       ctor() = delete;
       static std::shared_ptr<Tree> Leaf_() { return std::shared_ptr<Tree>(new Tree(Leaf{})); }
       static std::shared_ptr<Tree> Node_(std::shared_ptr<Tree> l, std::shared_ptr<Tree> r) { ... }
     };
   };
*)
let gen_ind_header_v2 ?(is_mutual=false) vars name cnames tys method_candidates ind_kind =
  let is_coinductive = ind_kind = Coinductive in
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in

  (* Handle empty inductives (no constructors) - generate uninhabitable struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate:
       struct empty {
         empty() = delete;
       };
       This type cannot be constructed, matching the semantics of empty types. *)
    let method_fields = List.map (gen_single_method name vars) method_candidates in
    Dstruct { ds_ref = name; ds_fields = [(Fdeleted_ctor, VPublic)] @ method_fields;
              ds_tparams = templates; ds_constraint = None }
  else

  (* Check if all constructors are nullary: eligible for enum class *)
  let all_nullary = Array.for_all (fun tys_list -> tys_list = []) tys in
  if all_nullary && vars = [] && not is_mutual && not (is_custom name) then begin
    (* Register as enum inductive for type/constructor/match generation *)
    Table.add_enum_inductive name;
    let ctor_names = Array.to_list (Array.map (fun c ->
      match c with
      | GlobRef.ConstructRef _ -> Id.of_string (Common.pp_global_name Type c)
      | _ -> Id.of_string ("Ctor" ^ string_of_int 0)
    ) cnames) in
    Denum { de_ref = name; de_ctors = ctor_names; de_tparams = [] }
  end
  else

  (* The main struct type: std::shared_ptr<Tree> or std::shared_ptr<Tree<A>> *)
  let self_ty = Tshared_ptr (Tglob (name, ty_vars, [])) in

  (* 1. Constructor alternative structs (simple, just fields, no make) *)
  let constructor_structs = Array.to_list (Array.mapi
    (fun i tys_list ->
      let c = cnames.(i) in
      let cname = match c with
        | GlobRef.ConstructRef ((_, _), _) ->
            (* Get constructor name from the GlobRef *)
            Id.of_string (Common.pp_global_name Type c)
        | _ -> Id.of_string ("Ctor" ^ string_of_int i)
      in
      (* Fields: convert types, using self_ty for recursive references *)
      let fields = List.mapi (fun j ty ->
        let cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars ty in
        (* For indexed inductives (no template params), erase unnamed Tvars to std::any *)
        let cpp_ty = if vars = [] then tvar_erase_type cpp_ty else cpp_ty in
        (* Field name: use descriptive names if available, otherwise _a0, _a1, etc. *)
        let field_name = Id.of_string ("_a" ^ string_of_int j) in
        (Fvar (field_name, cpp_ty), VPublic)
      ) tys_list in
      (Fnested_struct (cname, fields), VPublic)
    ) tys) in

  (* 2. variant_t type alias - use simple Id-based refs that match nested struct names *)
  (* Note: nested structs inherit template params from parent, so don't add <A> to them *)
  let variant_ty = Tvariant (Array.to_list (Array.mapi
    (fun i c ->
      let cname_id = match c with
        | GlobRef.ConstructRef _ -> Id.of_string (Common.pp_global_name Type c)
        | _ -> Id.of_string ("Ctor" ^ string_of_int i)
      in
      (* Use Tid for local nested struct types - no template args since they inherit *)
      Tid (cname_id, [])
    ) cnames)) in
  let variant_using = (Fnested_using (Id.of_string "variant_t", variant_ty), VPublic) in

  (* 3. Private variant member: v_ for inductive, lazy_v_ for coinductive *)
  let variant_member_name = if is_coinductive then "lazy_v_" else "v_" in
  let variant_member_ty = if is_coinductive
    then Tid (Id.of_string_soft "crane::lazy", [Tid (Id.of_string "variant_t", [])])
    else Tid (Id.of_string "variant_t", []) in
  let variant_member = (Fvar (Id.of_string variant_member_name, variant_member_ty), VPrivate) in

  (* 4. Private explicit constructors for each alternative *)
  (* Note: nested struct types don't need template args - they inherit from parent *)
  let private_ctors = Array.to_list (Array.mapi
    (fun i c ->
      let cname = match c with
        | GlobRef.ConstructRef _ -> Id.of_string (Common.pp_global_name Type c)
        | _ -> Id.of_string ("Ctor" ^ string_of_int i)
      in
      let param_name = Id.of_string "_v" in
      let param_ty = Tid (cname, []) in
      if is_coinductive then
        (* For coinductive: lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) *)
        let init_expr = CPPfun_call (CPPvar (Id.of_string_soft "crane::lazy<variant_t>"),
          [CPPfun_call (CPPvar (Id.of_string "variant_t"), [CPPmove (CPPvar param_name)])]) in
        let init_list = [(Id.of_string "lazy_v_", init_expr)] in
        (Fconstructor ([(param_name, param_ty)], init_list, true), VPrivate)
      else
        (* For inductive: v_(std::move(_v)) *)
        let init_list = [(Id.of_string "v_", CPPmove (CPPvar param_name))] in
        (Fconstructor ([(param_name, param_ty)], init_list, true), VPrivate)
    ) cnames) in

  (* For coinductive types, add private constructor accepting std::function<variant_t()> *)
  let lazy_ctor = if is_coinductive then
    let param_name = Id.of_string "_thunk" in
    let variant_t_ty = Tid (Id.of_string "variant_t", []) in
    let param_ty = Tfun ([], variant_t_ty) in
    let init_expr = CPPfun_call (CPPvar (Id.of_string_soft "crane::lazy<variant_t>"),
      [CPPmove (CPPvar param_name)]) in
    let init_list = [(Id.of_string "lazy_v_", init_expr)] in
    [(Fconstructor ([(param_name, param_ty)], init_list, true), VPrivate)]
  else [] in

  (* 5. Public ctor struct with factory methods.
     Each constructor gets two factory variants:
     - Cons_(...) returning shared_ptr (standard, used by default)
     - Cons_uptr(...) returning unique_ptr (used when escape analysis proves safety)
     Both have identical parameters and live inside the ctor struct, which has
     access to the private constructor. *)
  let self_uty = ind_ty_uptr name ty_vars in
  let mk_factory_method suffix ret_ty wrap_expr i tys_list =
    let c = cnames.(i) in
    let cname = match c with
      | GlobRef.ConstructRef _ -> Common.pp_global_name Type c
      | _ -> "Ctor" ^ string_of_int i
    in
    let factory_name = Id.of_string (cname ^ suffix) in
    let params = List.mapi (fun j ty ->
      let cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) (Refset'.add name Refset'.empty) vars ty in
      let cpp_ty = if vars = [] then tvar_erase_type cpp_ty else cpp_ty in
      let wrapped = match cpp_ty with
        | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, cpp_ty))
        | _ -> cpp_ty
      in
      (Id.of_string ("a" ^ string_of_int j), wrapped)
    ) tys_list in
    let ctor_args = List.mapi (fun j _ ->
      CPPvar (Id.of_string ("a" ^ string_of_int j))
    ) tys_list in
    let ctor_struct = CPPstruct_id (Id.of_string cname, [], ctor_args) in
    let new_expr = CPPnew (Tglob (name, ty_vars, []), [ctor_struct]) in
    let body = [Sreturn (Some (wrap_expr new_expr))] in
    (Ffundef (factory_name, Tmod (TMstatic, ret_ty), params, body), VPublic)
  in
  let inner_ty = Tglob (name, ty_vars, []) in
  let factory_methods = Array.to_list (Array.mapi
    (mk_factory_method "_" self_ty (fun e -> CPPshared_ptr_ctor (inner_ty, e)))
    tys) in
  let uptr_factory_methods = Array.to_list (Array.mapi
    (mk_factory_method "_uptr" self_uty (fun e -> CPPunique_ptr_ctor (inner_ty, e)))
    tys) in

  (* For coinductive types, add lazy_ factory method.
     lazy_ accepts std::function<shared_ptr<T>()> and adapts it to
     std::function<variant_t()> for the lazy constructor. *)
  let lazy_factory = if is_coinductive then
    let lazy_name = Id.of_string "lazy_" in
    let thunk_param_ty = Tfun ([], self_ty) in
    let params = [(Id.of_string "thunk", thunk_param_ty)] in
    let variant_t_ty = Tid (Id.of_string "variant_t", []) in
    let adapter_lambda = CPPlambda (
      [],
      Some variant_t_ty,
      [Sasgn (Id.of_string "_tmp", Some self_ty, CPPfun_call (CPPvar (Id.of_string "thunk"), []));
       Sreturn (Some (CPPfun_call (CPPvar (Id.of_string_soft "std::move"),
         [CPPfun_call (CPPvar (Id.of_string_soft "const_cast<variant_t&>"),
           [CPPmethod_call (CPPvar (Id.of_string "_tmp"), Id.of_string "v", [])])])))]
      , true) in
    let new_expr = CPPnew (Tglob (name, ty_vars, []),
      [CPPfun_call (CPPvar (Id.of_string_soft "std::function<variant_t()>"),
        [adapter_lambda])]) in
    let shared_ptr_expr = CPPshared_ptr_ctor (Tglob (name, ty_vars, []), new_expr) in
    let body = [Sreturn (Some shared_ptr_expr)] in
    [(Ffundef (lazy_name, Tmod (TMstatic, self_ty), params, body), VPublic)]
  else [] in

  (* Add deleted default constructor to ctor struct *)
  let ctor_struct_fields = (Fdeleted_ctor, VPublic) :: factory_methods @ uptr_factory_methods @ lazy_factory in
  let ctor_struct = (Fnested_struct (Id.of_string "ctor", ctor_struct_fields), VPublic) in

  (* Add public accessor for v_ to enable pattern matching from outside *)
  let v_accessor = if is_coinductive then
    (* For coinductive: const variant_t& v() const { return lazy_v_.force(); } *)
    (Fmethod {
      mf_name = Id.of_string "v";
      mf_tparams = [];
      mf_ret_type = Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", [])));
      mf_params = [];
      mf_body = [Sreturn (Some (CPPfun_call (CPPmember (CPPvar (Id.of_string "lazy_v_"), Id.of_string "force"), [])))];
      mf_is_const = true;
      mf_is_static = false;
    }, VPublic)
  else
    (* For inductive: const variant_t& v() const { return v_; } *)
    (Fmethod {
      mf_name = Id.of_string "v";
      mf_tparams = [];
      mf_ret_type = Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", [])));
      mf_params = [];
      mf_body = [Sreturn (Some (CPPvar (Id.of_string "v_")))];
      mf_is_const = true;
      mf_is_static = false;
    }, VPublic) in

  (* Add mutable accessor for reuse optimization (Phase 3).
     For non-coinductive types: variant_t& v_mut() { return v_; }
     Not generated for coinductive types (lazy evaluation complicates reuse). *)
  let v_mut_accessor = if is_coinductive then []
  else
    [(Fmethod {
      mf_name = Id.of_string "v_mut";
      mf_tparams = [];
      mf_ret_type = Tref (Tid (Id.of_string "variant_t", []));
      mf_params = [];
      mf_body = [Sreturn (Some (CPPvar (Id.of_string "v_")))];
      mf_is_const = false;
      mf_is_static = false;
    }, VPublic)] in

  (* 6. Generate methods from method candidates using shared helper *)
  let method_fields = List.map (gen_single_method name vars) method_candidates in

  (* Combine all fields in order:
     - Constructor structs (public)
     - variant_t using (public)
     - v_ member (private)
     - Private constructors
     - ctor struct (public)
     - v() accessor (public)
     - v_mut() accessor (public, non-coinductive only)
     - Methods (public)
  *)
  let all_fields =
    constructor_structs @
    [variant_using] @
    [variant_member] @
    private_ctors @
    lazy_ctor @
    [ctor_struct] @
    [v_accessor] @
    v_mut_accessor @
    method_fields
  in

  (* Just the struct itself - no extra namespace wrapper *)
  Dstruct { ds_ref = name; ds_fields = all_fields; ds_tparams = templates; ds_constraint = None }

(* Generate methods for eponymous records.
   Uses the shared gen_single_method helper for records where methods are
   generated directly on the module struct (which has record fields merged).
   name: the record's GlobRef (e.g., IndRef for CHT)
   vars: the type variables of the record (e.g., [K; V] for CHT<K, V>)
   method_candidates: list of (func_ref, body, type, this_position) tuples *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  List.map (gen_single_method name vars) method_candidates
