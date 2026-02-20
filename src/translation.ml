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

(* Track type variables (template parameters) in scope for the current function.
   When converting Tvar to C++ types, we use this to give them proper names. *)
let current_type_vars : Id.t list ref = ref []
let set_current_type_vars (tvars : Id.t list) = current_type_vars := tvars
let get_current_type_vars () = !current_type_vars
let clear_current_type_vars () = current_type_vars := []

(* Track parameter types for the current function.
   Maps de Bruijn indices to ML types. Used to refine pattern match types.
   The params list is in innermost-first order (from collect_lams), matching
   de Bruijn indexing where MLrel 1 is the first/innermost binding. *)
let current_param_types : (int * ml_type) list ref = ref []
let set_current_param_types (params : (Id.t * ml_type) list) =
  current_param_types := List.mapi (fun i (_, ty) ->
    (i + 1, ty)) params
let get_param_type_by_index (idx : int) : ml_type option =
  try Some (List.assoc idx !current_param_types)
  with Not_found -> None
let clear_current_param_types () = current_param_types := []

(* Track the current outer function name for generating lifted function names.
   When an inner fixpoint needs lifting, its name becomes _<outer>_<fix>. *)
let current_outer_function_name : string option ref = ref None

(* Accumulate lifted declarations (inner fixpoints promoted to top-level functions).
   These are collected during gen_stmts and emitted before the enclosing function. *)
let pending_lifted_decls : cpp_decl list ref = ref []
let add_lifted_decl (d : cpp_decl) = pending_lifted_decls := d :: !pending_lifted_decls
let take_lifted_decls () = let ds = List.rev !pending_lifted_decls in pending_lifted_decls := []; ds

(* Parallel type stack for the de Bruijn environment.
   Tracks (Id.t * ml_type) for each variable pushed via push_vars',
   in the same order as the env's db list (innermost first).
   Used to look up ML types of free variables when lifting polymorphic let helpers. *)
let env_types : (Id.t * ml_type) list ref = ref []
let push_env_types (ids : (Id.t * ml_type) list) =
  env_types := ids @ !env_types
let get_env_type (i : int) : ml_type = snd (List.nth !env_types (pred i))
let reset_env_types () = env_types := []

let ml_type_is_void : ml_type -> bool = function
| Tglob (r, _, _) -> is_void r
| _ -> false

(* ============================================================================
   Shared helpers for method generation (used by gen_ind_header_v2 and gen_record_methods)
   ============================================================================ *)

(* Collect all Tvar indices from an ml_type.
   Used to find type variables beyond those of the containing inductive/record. *)
let rec collect_tvars acc = function
  | Miniml.Tvar i | Miniml.Tvar' i -> if List.mem i acc then acc else i :: acc
  | Miniml.Tarr (t1, t2) -> collect_tvars (collect_tvars acc t1) t2
  | Miniml.Tglob (_, args, _) -> List.fold_left collect_tvars acc args
  | Miniml.Tmeta { contents = Some t } -> collect_tvars acc t
  | _ -> acc

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
  | _ -> e
and local_var_subst_stmt (target : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  match s with
  | Sreturn e -> Sreturn (local_var_subst_expr target repl e)
  | Sasgn (id, ty, e) -> Sasgn (id, ty, local_var_subst_expr target repl e)
  | Sexpr e -> Sexpr (local_var_subst_expr target repl e)
  | Scustom_case (ty, e, tys, brs, str) ->
      Scustom_case (ty, local_var_subst_expr target repl e, tys,
        List.map (fun (args, ty, stmts) ->
          (args, ty, List.map (local_var_subst_stmt target repl) stmts)) brs, str)
  | _ -> s

(* Build extended tvar names covering both signature and body Tvar indices.
   sig_indices: sorted list of Tvar indices from the function signature
   sig_names: corresponding Id.t names for those indices
   body_tvars: sorted-unique list of all Tvar indices found in the body *)
let build_extended_tvar_names sig_indices sig_names body_tvars =
  let n_sig = List.length sig_indices in
  let body_extra_tvars = List.filter (fun i -> not (List.mem i sig_indices)) body_tvars in
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
   convert_fn: function to convert ml_type -> cpp_type (typically convert_ml_type_to_cpp_type env [] tvar_names)
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

(* Extract argument types and return type from a function type. *)
let rec get_args_and_ret acc = function
  | Tarr (t, rest) -> get_args_and_ret (t :: acc) rest
  | ret_ty -> (List.rev acc, ret_ty)

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
  | Tstruct (r, tys) -> Tstruct (r, List.map tvar_erase_type tys)
  | Tref ty -> Tref (tvar_erase_type ty)
  | Tvariant tys -> Tvariant (List.map tvar_erase_type tys)
  | Tshared_ptr ty -> Tshared_ptr (tvar_erase_type ty)
  | Tid (id, tys) -> Tid (id, List.map tvar_erase_type tys)
  | Tqualified (ty, id) -> Tqualified (tvar_erase_type ty, id)
  | _ -> ty  (* Tvoid, Tstring, Ttodo, Tunknown, Taxiom, Tany *)

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
let rec collect_free_rels n_bound acc = function
  | MLrel i -> if i > n_bound && not (List.mem (i - n_bound) acc)
               then (i - n_bound) :: acc else acc
  | MLlam (_, _, body) -> collect_free_rels (n_bound + 1) acc body
  | MLletin (_, _, a, b) ->
      collect_free_rels n_bound (collect_free_rels (n_bound + 1) acc b) a
  | MLapp (f, args) ->
      List.fold_left (collect_free_rels n_bound) (collect_free_rels n_bound acc f) args
  | MLcase (_, e, brs) ->
      let acc = collect_free_rels n_bound acc e in
      Array.fold_left (fun acc (ids, _, _, body) ->
        collect_free_rels (n_bound + List.length ids) acc body) acc brs
  | MLfix (_, ids, funs, _) ->
      let n_fix = Array.length ids in
      Array.fold_left (fun acc f ->
        let params, body = collect_lams f in
        collect_free_rels (n_bound + List.length params + n_fix) acc body) acc funs
  | MLcons (_, _, args) -> List.fold_left (collect_free_rels n_bound) acc args
  | MLmagic a -> collect_free_rels n_bound acc a
  | MLtuple args -> List.fold_left (collect_free_rels n_bound) acc args
  | MLparray (arr, def) ->
      collect_free_rels n_bound (Array.fold_left (collect_free_rels n_bound) acc arr) def
  | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> acc

let rec convert_ml_type_to_cpp_type env (ns : GlobRef.t list) (tvars : Id.t list) (ml_t : ml_type) : cpp_type =
  match ml_t with
  | Tarr (t1, t2) -> (* FIX *)
        let t1c = convert_ml_type_to_cpp_type env ns tvars t1 in
        let t2c = convert_ml_type_to_cpp_type env ns tvars t2 in
        if isTdummy t1 then t2c else
        (match t2c with
        | Tfun (l, t) -> Tfun (t1c::l, t)
        | _ -> Tfun (t1c::[], t2c))
  | Tglob (g, _, _) when is_void g -> Tvoid
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
                let is_local = List.exists (Environ.QGlobRef.equal Environ.empty_env g) ns ||
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
          let is_local = List.exists (Environ.QGlobRef.equal Environ.empty_env g) ns ||
                         List.exists (Environ.QGlobRef.equal Environ.empty_env g) !local_inductives in
          if is_local then core
          else Tnamespace (g, core)
        else
        (* Check if this inductive is in the explicit ns list or in local_inductives context *)
        let is_local = List.exists (Environ.QGlobRef.equal Environ.empty_env g) ns ||
                       List.exists (Environ.QGlobRef.equal Environ.empty_env g) !local_inductives in
        if is_local then Tshared_ptr core
        else if not (get_record_fields g == []) then Tshared_ptr core
        else Tshared_ptr (Tnamespace (g, core))
      | _ -> core)
  | Tvar i | Tvar' i ->
      (try Tvar (i, Some (List.nth tvars (pred i)))
       with Failure _ -> Tvar (i, None))
  | Tstring -> assert false (* TODO: get rid of Tstring in both ASTs *)
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ns tvars t
  | Tmeta {id = i} ->
      (* Unresolved meta - use std::any for type erasure.
         This happens for existential type variables in indexed inductives. *)
      Tany
  | Tdummy Ktype -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_type")), [], [])
  | Tdummy Kprop -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_prop")), [], [])
  | Tdummy (Kimplicit _) -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_implicit")), [], [])
  | Tunknown -> Tany
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string ("axiom")), [], [])
  (*
      let _ = print_endline "TODO: TMETA OR TDUMMY OR TUNKNOWN OR TAXIOM"  in
      assert false *)

(* TODO: when an MLGlob has monadic type, needs to be funcall *)
and gen_expr env (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i -> (try (CPPvar (get_db_name i env)) with Failure _ -> CPPvar' i)
  | MLapp (MLmagic t, args) -> gen_expr env (MLapp (t, args))
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    let t = Common.last (a1 :: l) in
    gen_expr env t
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
    gen_expr env (MLapp (a1, a2::[])) *)
  | MLapp (f, args) ->
    eta_fun env f args
  | MLlam _ as a ->
      let args,a = collect_lams a in
      let lam_params = List.map (fun (x, y) -> (id_of_mlid x, y)) args in
      let args,env = push_vars' lam_params env in
      let saved_env_types = !env_types in
      push_env_types args;
      let args = List.filter (fun (_,ty) -> not (isTdummy ty)) args in (* TODO: this could cause issues. TEST. *)
      let tvars = get_current_type_vars () in
      let args = List.map (fun (id, ty) -> (convert_ml_type_to_cpp_type env [] tvars ty, Some id)) args in
      let f = CPPlambda (args, None, gen_stmts env (fun x -> Sreturn x) a, false) in
      env_types := saved_env_types;
      (match args with
      | [] -> CPPfun_call (f, [])
      | _ -> f)
  | MLglob (x, tys) when is_inline_custom x ->
      let tvars = get_current_type_vars () in
      let ty = find_type x in
      let ty = convert_ml_type_to_cpp_type env [] tvars ty in
      (match ty with
      | Tfun (dom, cod) -> eta_fun env (MLglob (x, tys)) [] (* TODO: cound be only if contains '%' *)
      | _ -> CPPglob (x, List.map (convert_ml_type_to_cpp_type env [] tvars) tys))
  | MLglob (x, tys) ->
      let tvars = get_current_type_vars () in
      CPPglob (x, List.map (convert_ml_type_to_cpp_type env [] tvars) tys)
  | MLcons (ty, r, ts) when is_custom r ->
    let args = List.rev_map (gen_expr env) ts in
    let app x = (match args with
      | [] -> x
      | _ -> CPPfun_call(x, args)) in
    (match ty with
    | Tglob (n, tys, _) ->
      (* Filter out index type args - only keep parameters *)
      let tys = match n with
        | GlobRef.IndRef (kn, _) ->
            (match Table.get_ind_num_param_vars_opt kn with
            | Some num_param_vars -> List.firstn num_param_vars tys
            | None -> tys)
        | _ -> tys
      in
      let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
      app (CPPglob (r, temps))
    | _ -> app (CPPglob (r, [])))
  | MLcons (ty, r, ts) when ts = [] && (match r with GlobRef.ConstructRef ((kn, _), _) -> is_enum_inductive (GlobRef.IndRef (kn, 0)) | _ -> false) ->
    (* Enum constructor: emit bare EnumType::Constructor value *)
    let ctor_name = Id.of_string (Common.pp_global_name Type r) in
    let ind_ref = (match r with GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i) | _ -> assert false) in
    CPPenum_val (ind_ref, ctor_name)
  | MLcons (ty, r, ts) ->
    let fds = record_fields_of_type ty in
    (match fds with
      | [] ->
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
        let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
        (* Get the constructor base name (without module path) and add underscore suffix *)
        let ctor_name = Common.pp_global_name Type r in
        let factory_name = Id.of_string (ctor_name ^ "_") in
        (* Build: Type<temps>::ctor::Factory_(args) *)
        let type_expr = CPPglob (n, temps) in
        let ctor_expr = CPPqualified (type_expr, Id.of_string "ctor") in
        let factory_expr = CPPqualified (ctor_expr, factory_name) in
        CPPfun_call (factory_expr, args)
      | _ ->
        (* Fallback for non-Tglob types - shouldn't happen in practice *)
        let ctor_name = Common.pp_global_name Type r in
        let factory_name = Id.of_string (ctor_name ^ "_") in
        let ctor_expr = CPPqualified (CPPglob (r, []), Id.of_string "ctor") in
        let factory_expr = CPPqualified (ctor_expr, factory_name) in
        CPPfun_call (factory_expr, args)) in
      (* Note: CPPfun_call reverses args when printing, so we reverse here *)
      gen_ctor_call (List.rev_map (gen_expr env) ts)
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
        let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
        CPPfun_call (CPPmk_shared (Tglob (n, temps, [])), [CPPstruct (n, temps, args)])
      | _ -> assert false) in
      nstempmod (List.map (gen_expr env) ts))
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let cexp = gen_custom_cpp_case env (fun x -> Sreturn x) typ t pv in
    CPPfun_call (CPPlambda([], None, [cexp], false), [])
  (* TODO: SLOPPY and incomplete *)
  | MLcase (typ, t, pv) when not (record_fields_of_type typ == []) && Array.length pv == 1 ->
    let (ids,r,pat,body) = pv.(0) in
    let n = List.length ids in
    (* For type classes, use qualified access (::) instead of arrow (->) since
       type class instances are template type parameters, not runtime values *)
    let is_typeclass = Table.is_typeclass_type typ in
    let make_field_access base_expr fld =
      if is_typeclass then
        let fld_name = Id.of_string (Common.pp_global_name Term fld) in
        CPPqualified (base_expr, fld_name)
      else
        CPPget' (base_expr, fld)
    in
    (match body with
    | MLrel i when i <= n ->
      let fld = List.nth (record_fields_of_type typ) (n - i) in
      (match fld with
      | Some fld -> make_field_access (gen_expr env t) fld
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | MLapp (MLrel i, args) when i <= n ->
      let fld = List.nth (record_fields_of_type typ) (n - i) in
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (match fld with
      (* CPPfun_call expects args in reverse order; List.rev_map both converts and reverses *)
      | Some fld -> CPPfun_call (make_field_access (gen_expr env t) fld, List.rev_map (gen_expr env') args)
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | _ ->
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let asgns = List.mapi (fun i (id, ty) ->
        let fld = List.nth (record_fields_of_type typ) i in
        let e = (match fld with
          | Some fld -> make_field_access (gen_expr env t) fld
          | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj")) in
        Sasgn (remove_prime_id (id_of_mlid id), Some (convert_ml_type_to_cpp_type env [] [] ty), e)) ids in
      CPPfun_call (CPPlambda([], None, asgns @ gen_stmts env' (fun x -> Sreturn x) body, false), []))
      (* TODO: ugly. should better attempt when generating statements! *)
      (* TODO: we don't currently support the fancy thing of pattern matching on record fields at the same time *)
  | MLcase (typ, t, pv) when lang () == Cpp -> gen_cpp_case typ t env pv
  (* | MLcase (typ, t, pv) when lang () == Rust -> gen_rust_case typ t env pv *)
  | MLletin (_, ty, _, _) as a -> CPPfun_call (CPPlambda([], None, gen_stmts env (fun x -> Sreturn x) a, false), [])
  (*| MLfix _ -> CPPvar (Id.of_string "FIX")*)
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic t -> gen_expr env t
  | MLdummy _ ->
    CPPstring (Pstring.unsafe_of_string "dummy")
  | MLexn msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    CPPabort msg
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
    | _ -> false
  in
  match f with
  | MLglob (id , tys) ->
    (* Partition args into type class instances and regular args *)
    let (typeclass_ml_args, regular_ml_args) =
      List.partition is_typeclass_instance_arg args in
    (* Reverse typeclass args to match template param order from gen_dfun:
       gen_dfun iterates collect_lams output (reversed from source) so the first
       typeclass in that order becomes 'i'. Call sites have args in source order,
       so we reverse to match. *)
    let typeclass_ml_args = List.rev typeclass_ml_args in
    (* Convert type class instance args to template type arguments *)
    let typeclass_type_args = List.map (fun ml_arg ->
      match ml_arg with
      | MLglob (r, ts) ->
          (* Use the instance struct as a type - convert to Tglob *)
          Tglob (r, List.map (convert_ml_type_to_cpp_type env [] []) ts, [])
      | MLrel i ->
          (* The instance is a lambda parameter - look up its name in the env
             and create a Tvar reference to the template parameter *)
          let (db, _) = env in
          let name = List.nth db (pred i) in
          Tvar (0, Some name)
      | _ -> assert false  (* Already filtered by is_typeclass_instance_arg *)
    ) typeclass_ml_args in
    (* Generate regular args as expressions *)
    let args = List.map (gen_expr env) regular_ml_args in
    let ty = find_type id in
    let ty = try (type_subst_list tys ty) with _ -> ty in (* TODO : make less hacky; do a type_subst that can't fail *)
    let tvars = get_current_type_vars () in
    let ty = convert_ml_type_to_cpp_type env [] tvars ty in
    (* Combine: instance types first, then regular type args *)
    let all_type_args = typeclass_type_args @ (List.map (convert_ml_type_to_cpp_type env [] tvars) tys) in
    let cglob = CPPglob (id, all_type_args) in
    (match ty with
    | Tfun (dom, cod) ->
      (* Filter domain to exclude type class types (they're now template params) *)
      let dom = List.filter (fun t -> not (Table.is_typeclass_type_cpp t)) dom in
      let missing_args = get_eta_args dom args in
      if missing_args == [] then CPPfun_call (cglob, List.rev args) else
      let eta_args = List.mapi (fun i ty -> (Tmod (TMconst, ty), Some (Id.of_string ("_x" ^ string_of_int i)))) missing_args in
      let call_args = args @
         List.mapi (fun i _ -> (CPPvar (Id.of_string ("_x" ^ string_of_int i)))) eta_args in
      CPPlambda (List.rev eta_args, None,[Sreturn (CPPfun_call (cglob, List.rev call_args))], false)
    | _ ->
      (* print_endline ("NOT A FUN" ^ Pp.string_of_ppcmds (GlobRef.print id) ^ string_of_int (List.length args)) ; *)
      CPPfun_call (cglob, args))
  | _ ->
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
  (* Get type arguments from scrutinee to substitute in branch types *)
  let type_args = match typ with
    | Tglob (_, tys, _) -> tys
    | _ -> []
  in
  (* Substitute type variables in return type and argument types *)
  let rty = if type_args <> [] then
    (try type_subst_list type_args rty with _ -> rty)
    else rty
  in
  let ids = List.map (fun (id, ty) ->
    let ty = if type_args <> [] then
      (try type_subst_list type_args ty with _ -> ty)
      else ty
    in
    (id, ty)) ids
  in
  (* Build path: typename InductiveType<temps>::ConstructorName *)
  let constr = match typ with
  | Tglob (r, tys, _) ->
    (* Simplify ML types first, then substitute type variables, then convert to C++ *)
    let tys = List.map type_simpl tys in
    let tys = if type_args <> [] then
      List.map (fun ty -> try type_subst_list type_args ty with _ -> ty) tys
      else tys
    in
    (* Filter out index type args - only keep parameters *)
    let tys = match r with
      | GlobRef.IndRef (kn, _) ->
          (match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars -> List.firstn num_param_vars tys
          | None -> tys)
      | _ -> tys
    in
    let temps = List.map (convert_ml_type_to_cpp_type env [] tvars) tys in
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
  let ret = convert_ml_type_to_cpp_type env [] tvars rty in
  (* For pattern matching lambdas, if the return type would be an unnamed Tvar
     (like T1, T2 which are not actual template parameters), use 'auto' instead.
     C++ can deduce the return type from the return statements. *)
  let ret = match ret with
    | Minicpp.Tvar (_, None) -> Minicpp.Ttodo  (* Ttodo prints as 'auto' *)
    | _ -> ret
  in
  let asgns =  List.mapi (fun i x ->
      let id = Id.of_string ("_a" ^ string_of_int i) in
      let cpp_ty = convert_ml_type_to_cpp_type env [] tvars (snd x) in
      (* Only erase Tvars in constructor field types for indexed inductives *)
      let cpp_ty = if is_indexed_ind then tvar_erase_type cpp_ty else cpp_ty in
      Sasgn (fst x, Some cpp_ty, CPPget (CPPglob (GlobRef.VarRef sname, []), id))) (List.rev ids) in
  let asgns = List.filteri (fun i _ -> List.nth dummies i) asgns in
  CPPlambda(
        [(Tmod (TMconst, constr), Some sname)],
        Some ret,
        asgns @ gen_stmts env (fun x -> Sreturn x) body, false)

and gen_cpp_case (typ : ml_type) t env pv =
  (* When scrutinee is a parameter reference, use parameter's concrete type if available.
     This handles monomorphic functions where MLcase has Tvar but parameter is concrete. *)
  let typ = match t with
    | MLrel i | MLmagic (MLrel i) ->
        (match get_param_type_by_index i with
         | Some (Miniml.Tglob (r2, _, _) as param_ty) ->
             (match typ with
              | Miniml.Tglob (r1, _, _)
                when Environ.QGlobRef.equal Environ.empty_env r1 r2
                  && has_tvar typ && not (has_tvar param_ty) ->
                  param_ty
              | _ -> typ)
         | _ -> typ)
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
        | Pusual r ->
          let _ids', env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
          let ctor_name = Id.of_string (Common.pp_global_name Type r) in
          let body_stmts = gen_stmts env' (fun x -> Sreturn x) body in
          (ctor_name, body_stmts) :: gen_enum_branches cs
        | _ -> raise TODO)
    in
    let branches = gen_enum_branches (Array.to_list pv) in
    CPPfun_call (CPPlambda ([], None, [Sswitch (scrutinee, ind_ref, branches)], false), [])
  else
  (* Call v() accessor method to get the variant for pattern matching *)
  let outer cases x = (CPPfun_call (CPPvisit, CPPmethod_call (x, Id.of_string "v", []) :: [CPPoverloaded cases])) in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let saved_env_types = !env_types in
      push_env_types ids';
      let dummies = List.map (fun (x,_) ->
        match x with
        | Dummy -> false
        | _ -> true) ids in
      let br = gen_cpp_pat_lambda env' typ rty r ids' dummies t in
      env_types := saved_env_types;
      br :: (gen_cases cs)
    | _ -> raise TODO) in
  outer (gen_cases (Array.to_list pv)) (gen_expr env t)

and gen_rust_case (typ : ml_type) t env pv =
  let outer cases x = (CPPmatch (x, cases)) in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let saved_env_types = !env_types in
      push_env_types ids';
      let temps = begin match typ with
        | Tglob (r, tys, _) -> List.map (convert_ml_type_to_cpp_type env [] []) tys
        | _ -> []
        end in
      let c = begin match ids' with
       | [] -> CPPglob (r, temps)
       | _ -> CPPfun_call(CPPglob (r, temps), List.map (fun (x, _) -> CPPvar x) ids')
       end in
      let br = (c, gen_expr env' t) in
      env_types := saved_env_types;
      br :: (gen_cases cs)
    | _ -> raise TODO) in
  outer (gen_cases (Array.to_list pv)) (gen_expr env t)

and gen_cpp_custom_body env k rty ids body =
  let tvars = get_current_type_vars () in
  let ret = convert_ml_type_to_cpp_type env [] tvars rty in
  let ids =  List.map (fun (x, ty) -> (x, convert_ml_type_to_cpp_type env [] tvars ty)) (List.rev ids) in
  let body = gen_stmts env k body in
  (ids, ret, body)

and gen_custom_cpp_case env k (typ : ml_type) t pv =
  let tvars = get_current_type_vars () in
  let temps = match typ with
  | Tglob (r, tys, _) ->
    List.map (convert_ml_type_to_cpp_type env [] tvars) tys
  | _ -> [] in
  let typ = convert_ml_type_to_cpp_type env [] tvars typ in
  let t = gen_expr env t in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let saved_env_types = !env_types in
      push_env_types ids';
      let br = gen_cpp_custom_body env' k rty ids' t in
      env_types := saved_env_types;
      br :: (gen_cases cs)
    | _ -> raise TODO) in
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
    let outer_name = match !current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
    (* Save and set current_type_vars to the full tvar list for the lifted function *)
    let saved_tvars = get_current_type_vars () in
    set_current_type_vars all_tvar_names;
    (* Generate the fixpoint body using gen_fix *)
    let funs_compiled = Array.to_list (Array.map2 (gen_fix env) ids funs) in
    (* Restore outer type vars *)
    set_current_type_vars saved_tvars;
    (* Build a lifted Dfundef for each fixpoint function (usually just one) *)
    List.iteri (fun i ((renamed_id, fix_ty), params, body) ->
      let cpp_ty = convert_ml_type_to_cpp_type env [] all_tvar_names fix_ty in
      let (_, cod) = match cpp_ty with
        | Tfun (dom, cod) -> (dom, cod)
        | _ -> ([], cpp_ty) in
      let (cpp_params, all_temps_with_funs) =
        build_lifted_cpp_params (convert_ml_type_to_cpp_type env [] all_tvar_names) all_temps params in
      (* Replace recursive self-references (CPPvar renamed_n) with calls to the lifted function *)
      let rec_call = CPPglob (lifted_ref, List.map (fun id -> Tvar (0, Some id)) all_tvar_names) in
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
    (* Generate b, then replace references to the fixpoint var with calls to the lifted function. *)
    let outer_type_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
    let lifted_call = CPPglob (lifted_ref, outer_type_args) in
    let result = gen_stmts env_with_fix k b in
    List.map (local_var_subst_stmt fix_name lifted_call) result
  end else begin
    (* No extra Tvars - proceed with original local fixpoint approach *)
    (* Call gen_fix with original names - it will handle renaming internally *)
    let funs_compiled = Array.to_list (Array.map2 (gen_fix env) ids funs) in
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
      Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env [] tvars ty))) renamed_ids in
    let ret_ty ty = (match convert_ml_type_to_cpp_type env [] tvars ty with
      | Tfun (_,t) ->
          (match t with
          | Minicpp.Tvar (_, None) -> None
          | _ -> Some t)
      | _ -> None) in
    (* Use renamed ids for definitions *)
    let defs = List.map2 (fun (id, fty) (args, body) ->
      Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env [] tvars ty, Some id) args, ret_ty fty, body, false))) renamed_ids funs_with_params in
    (* Add renamed ids to environment for processing body *)
    let _, env_with_fix = push_vars' renamed_ids env in
    push_env_types renamed_ids;
    decls @ defs @ gen_stmts env_with_fix k b
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
    let _,env' = push_vars' [x', t] env in
    push_env_types [x', t];
    if x == Dummy then gen_stmts env' k b else
    let afun v = Sasgn (x', None, v) in
    let asgn = gen_stmts env afun a in
    let tvars = get_current_type_vars () in
    match asgn with
    | [ Sasgn (x', None, e) ] -> Sasgn (x', Some (convert_ml_type_to_cpp_type env [] tvars t), e) :: gen_stmts env' k b
    | _ ->
      Sdecl (x', convert_ml_type_to_cpp_type env [] tvars t) :: asgn @ gen_stmts env' k b
  in
  if not has_extra then gen_normal_letin ()
  else begin
    (* Lift the polymorphic lambda to a top-level template function. *)
    let params, body = collect_lams a in
    let n_params = List.length params in
    let x' = remove_prime_id (id_of_mlid x) in

    (* 1. Collect free variables in the lambda body *)
    let free_indices = collect_free_rels n_params [] body in
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
    let outer_name = match !current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string x' in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in

    (* 4. Substitution helper for call sites: replace CPPfun_call(CPPvar x', args) with
       CPPfun_call(CPPglob(lifted_ref, []), free_var_cpps @ args) *)
    let rec subst_lifted_call_expr (target : Id.t) (lifted : GlobRef.t) (free_args : cpp_expr list) (e : cpp_expr) =
      let sub = subst_lifted_call_expr target lifted free_args in
      match e with
      | CPPfun_call (CPPvar id, args) when Id.equal id target ->
          CPPfun_call (CPPglob (lifted, []), free_args @ List.map sub args)
      | CPPvar id when Id.equal id target ->
          (* Bare reference to lifted function: if there are free args, wrap in a lambda *)
          if free_args = [] then
            CPPglob (lifted, [])
          else
            (* Generate a lambda that captures and forwards: [&]() { return lifted(free_args...); } *)
            CPPlambda ([], None, [Sreturn (CPPfun_call (CPPglob (lifted, []), free_args))], false)
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
      | Sreturn e -> Sreturn (subst_lifted_call_expr target lifted free_args e)
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
    let saved_env_types = !env_types in
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
    env_types := saved_env_types;
    push_env_types lam_param_ids;
    let compiled_body = gen_stmts lam_env (fun x -> Sreturn x) body in
    env_types := saved_env_types;
    set_current_type_vars saved_tvars;

    (* 7. Now substitute free variable references in compiled body:
       Free vars in the body were compiled as CPPvar(name_from_outer_env).
       In the lifted function, they become parameters. The names are the same,
       so no substitution of the body is needed — the free var params have the same
       names as the outer scope variables. *)

    (* 8. Build the lifted function parameters: free vars first, then lambda params *)
    let all_lifted_params = free_var_params @ (List.filter (fun (_, ty) -> not (ml_type_is_void ty) && not (isTdummy ty)) lam_param_ids) in
    let (cpp_params, all_temps_with_funs) =
      build_lifted_cpp_params (convert_ml_type_to_cpp_type lam_env [] extended_tvar_names) all_temps all_lifted_params in

    (* Get return type from the let-binding type *)
    let cpp_ty = convert_ml_type_to_cpp_type lam_env [] extended_tvar_names t in
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
    let cont = gen_stmts env' k b in
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
  let afun v = Sasgn (x_renamed, None, v) in
  let asgn = gen_stmts env afun a in
  let tvars = get_current_type_vars () in
  begin match asgn with
  | [ Sasgn (_, None, e) ] -> Sasgn (x_renamed, Some (convert_ml_type_to_cpp_type env [] tvars t), e) :: gen_stmts env' k b
  | _ ->
    Sdecl (x_renamed, convert_ml_type_to_cpp_type env [] tvars t) :: asgn @ gen_stmts env' k b
  end
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
    let outer_name = match !current_outer_function_name with
      | Some n -> n | None -> "anon" in
    let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
    let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
    (* Save and set current_type_vars to the extended tvar list for the lifted function.
       extended_tvar_names covers both signature and body Tvar indices. *)
    let saved_tvars = get_current_type_vars () in
    set_current_type_vars extended_tvar_names;
    let funs_compiled = Array.to_list (Array.map2 (gen_fix env) ids funs) in
    set_current_type_vars saved_tvars;
    (* Build lifted declarations *)
    List.iteri (fun i ((renamed_id, fix_ty), params, body) ->
      let cpp_ty = convert_ml_type_to_cpp_type env [] extended_tvar_names fix_ty in
      let (_, cod) = match cpp_ty with
        | Tfun (dom, cod) -> (dom, cod)
        | _ -> ([], cpp_ty) in
      let (cpp_params, all_temps_with_funs) =
        build_lifted_cpp_params (convert_ml_type_to_cpp_type env [] extended_tvar_names) all_temps params in
      let rec_call = CPPglob (lifted_ref, List.map (fun id -> Tvar (0, Some id)) all_tvar_names) in
      let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
      let inner = Dfundef ([lifted_ref, []], cod, cpp_params, body) in
      let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
      add_lifted_decl lifted_decl
    ) funs_compiled;
    (* Generate args in outer scope and call the lifted function.
       With template function parameters (F0 &&), C++ can deduce all type args. *)
    let cpp_args = List.rev_map (gen_expr env) args in
    [k (CPPfun_call (CPPglob (lifted_ref, []), cpp_args))]
  end else begin
    (* No extra Tvars - proceed with original local fixpoint approach *)
    let funs_compiled = Array.to_list (Array.map2 (gen_fix env) ids funs) in
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
      Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env [] tvars ty))) renamed_ids in
    let ret_ty ty = (match convert_ml_type_to_cpp_type env [] tvars ty with
      | Tfun (_,t) ->
          (match t with
          | Minicpp.Tvar (_, None) -> None
          | _ -> Some t)
      | _ -> None) in
    let defs = List.map2 (fun (id, fty) (params, body) -> Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env [] tvars ty, Some id) params, ret_ty fty, body, false))) renamed_ids funs_with_params in
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
  (* Call gen_fix with original names - it will handle renaming internally *)
  let funs_compiled = Array.to_list (Array.map2 (gen_fix env) ids funs) in
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
    Sdecl (id, fix_func_type (convert_ml_type_to_cpp_type env [] tvars ty))) renamed_ids in
  let ret_ty ty = (match convert_ml_type_to_cpp_type env [] tvars ty with
    | Tfun (_,t) ->
        (match t with
        | Minicpp.Tvar (_, None) -> None
        | _ -> Some t)
    | _ -> None) in
  let defs = List.map2 (fun (id, fty) (params, body) -> Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env [] tvars ty, Some id) params, ret_ty fty, body, false))) renamed_ids funs_with_params in
  (* Return the fix function itself (for use in let bindings etc.) *)
  decls @ defs @ [k (CPPvar (fst (List.nth renamed_ids x)))]
(* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
  gen_stmts env k (MLapp (a1, a2::[])) *)
| MLapp (MLglob (r, bind_tys), a1 :: a2 :: l) when is_bind r ->
  let (a, f) = Common.last_two (a1 :: a2 :: l) in
  let a = gen_expr env a in
  let ids',f = collect_lams f in
  (* Resolve metas in continuation parameter types using bind's type arguments.
     bind has type forall A B, IO A -> (A -> IO B) -> IO B
     The first type argument is A, which is the type of the continuation parameter.
     Use mgu to unify them, which mutably resolves metas. *)
  let () = match bind_tys with
    | elem_ty :: _ ->
        List.iter (fun (_, ty) -> try_mgu ty elem_ty) ids'
    | [] -> ()
  in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids') env in
  push_env_types ids;
  (match ids with
  | (x, ty) :: _ ->
    let tvars = get_current_type_vars () in
    let ty = convert_ml_type_to_cpp_type env [] tvars ty in
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
  [SreturnVoid]
| MLexn msg ->
  (* Generate throw statement for unreachable/absurd cases (e.g., empty match) *)
  [Sthrow msg]
| MLmagic (MLexn msg) ->
  (* Handle MLexn wrapped in MLmagic *)
  [Sthrow msg]
| t -> [k (gen_expr env t)]

and gen_fix env (n,ty) f =
  let ids, f = collect_lams f in
  let ids,_ = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
  (* Push the fix function name, which may be renamed to avoid shadowing *)
  let renamed_fix_ids, env = push_vars' (ids @ [(n,ty)]) env in
  let saved_env_types = !env_types in
  push_env_types (ids @ [(n,ty)]);
  let renamed_n = fst (List.hd (List.rev renamed_fix_ids)) in
  let ids = List.filter (fun (_,ty) -> not (ml_type_is_void ty)) ids in
  let result = (renamed_n, ty), ids, gen_stmts env (fun x -> Sreturn x) f in
  env_types := saved_env_types;
  result

(* TODO: REDO NAMESPACE AS PART OF NAMES!!! *)

let gen_ind_cpp vars name cnames tys =
  let constrdecl = List.map snd (List.filter fst (Array.to_list (Array.mapi
    (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) [name] vars x)) tys in
      let make_args = List.map(fun (x,_) -> CPPglob (GlobRef.VarRef x, [])) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make = Dfundef ([c, []; GlobRef.VarRef (Id.of_string "make"), []], Tshared_ptr (Tglob (name, ty_vars, [])), List.rev constr,
        [Sreturn (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)]))]) in
      (ty_vars == [], make))
    tys))) in
  Dnspace (Some name, constrdecl)

let gen_record_cpp name fields ind =
  let l = List.combine fields ind.ip_types.(0) in
  let l = List.mapi (fun i (x, t) ->
    let n = match x with
    | Some n -> n
    | None -> GlobRef.VarRef (Id.of_string ("_field" ^ (string_of_int i))) in
    (Fvar' (n, convert_ml_type_to_cpp_type (empty_env ()) [] ind.ip_vars t), VPublic)) l in
  let ty_vars = List.map (fun x -> (TTtypename, x)) ind.ip_vars in
  match ty_vars with
  | [] -> Dstruct (name, l)
  | _ -> Dtemplate (ty_vars, None, Dstruct (name, l))

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
  (* Type vars become template parameters after the instance parameter *)
  let ty_vars = List.map (fun x -> (TTtypename, x)) ind.ip_vars in
  let all_params = (TTtypename, inst_id) :: ty_vars in
  (* Generate requires clauses for each method *)
  let method_list = List.combine fields ind.ip_types.(0) in
  (* Convert a type to a list of argument types and a return type *)
  let rec get_args_and_ret acc = function
    | Miniml.Tarr (arg, rest) -> get_args_and_ret (arg :: acc) rest
    | ret -> (List.rev acc, ret)
  in
  (* Generate a single method requirement *)
  let gen_method_req i (field_opt, field_ty) =
    match field_opt with
    | None -> None  (* Anonymous field, skip *)
    | Some field_ref ->
        let (args, ret) = get_args_and_ret [] field_ty in
        (* Filter out type class instance arguments (they're passed via template) *)
        let args = List.filter (fun t -> not (Table.is_typeclass_type t)) args in
        let ret_cpp = convert_ml_type_to_cpp_type (empty_env ()) [] ind.ip_vars ret in
        (* Create parameter names: a0, a1, a2, ... *)
        let params = List.mapi (fun j arg_ty ->
          let arg_cpp = convert_ml_type_to_cpp_type (empty_env ()) [] ind.ip_vars arg_ty in
          (arg_cpp, Id.of_string ("a" ^ string_of_int j))
        ) args in
        (* Method call: I::method_name(a0, a1, ...) *)
        let method_name = Common.pp_global_name Term field_ref in
        let call_args = List.map (fun (_, id) -> CPPvar id) params in
        let call = CPPfun_call (
          CPPqualified (CPPvar inst_id, Id.of_string method_name),
          call_args
        ) in
        (* Constraint: use the cpp_type directly - cpp.ml will render it *)
        let constraint_expr = CPPconvertible_to ret_cpp in
        Some (params, (call, constraint_expr))
  in
  let method_reqs = List.filter_map (fun pair -> gen_method_req 0 pair) method_list in
  (* Collect all unique parameter types for the requires clause *)
  let all_params_flat = List.concat_map fst method_reqs in
  (* Deduplicate parameters by keeping first occurrence of each type+name combination *)
  let seen = ref [] in
  let dedup_params = List.filter (fun (ty, id) ->
    let key = (ty, Id.to_string id) in
    if List.mem key !seen then false
    else (seen := key :: !seen; true)
  ) all_params_flat in
  let constraints = List.map snd method_reqs in
  let requires_expr = CPPrequires (dedup_params, constraints) in
  Dtemplate (all_params, None, Dconcept (name, requires_expr))

(* Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct (name : GlobRef.t) (body : ml_ast) (ty : ml_type)
    : cpp_decl option * GlobRef.t option * ml_type list =
  (* Check if the type is a type class type *)
  match ty with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref ->
      (* Get the type class fields (method names) and field types (from ind_packet) *)
      let fields = Table.record_fields_of_type ty in
      let field_types = Table.record_field_types class_ref in
      (match body with
      | MLcons (_, _ctor_ref, method_bodies) ->
          (* Generate static methods for each field *)
          let gen_method (field_ref, field_ml_ty) field_body =
            match field_ref with
            | None -> None  (* Anonymous field, skip *)
            | Some method_ref ->
                let method_name = Id.of_string (Common.pp_global_name Term method_ref) in
                (* Substitute type class parameter with instance's type arg in the field type.
                   This gives us the concrete return type (e.g., bool for eqb: A -> A -> bool). *)
                let subst_ty = Mlutil.type_subst_list type_args field_ml_ty in
                (* Extract return type by stripping Tarr's *)
                let rec get_ret = function
                  | Tarr (_, rest) -> get_ret rest
                  | ret -> ret
                in
                let method_ret_ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] (get_ret subst_ty) in
                (* Extract parameter names and types from the lambda *)
                let rec extract_params ml_acc cpp_acc body =
                  match body with
                  | MLlam (id, ty, rest) ->
                      let param_name = id_of_mlid id in
                      let param_cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
                      extract_params ((param_name, ty) :: ml_acc) ((param_name, param_cpp_ty) :: cpp_acc) rest
                  | _ -> (List.rev ml_acc, List.rev cpp_acc, body)
                in
                let (ml_params, cpp_params, inner_body) = extract_params [] [] field_body in
                (* If no lambdas found, the body is a function reference (like PrimInt63.eqb).
                   We need to eta-expand: generate parameters based on the method type,
                   then call the function with those parameters. *)
                let (cpp_params, ret_ty, body_stmts) =
                  if ml_params = [] then
                    match inner_body with
                    | MLglob (_fn_ref, _) ->
                        (* Eta-expand: generate parameters based on type args *)
                        let a_ty = List.hd type_args in
                        let a_cpp = convert_ml_type_to_cpp_type (empty_env ()) [] [] a_ty in
                        let p0 = Id.of_string "x" in
                        let p1 = Id.of_string "y" in
                        let call_expr = MLapp (inner_body, [MLrel 2; MLrel 1]) in
                        let env = snd (push_vars' [(p1, a_ty); (p0, a_ty)] (empty_env ())) in
                        let stmts = gen_stmts env (fun x -> Sreturn x) call_expr in
                        ([(p0, a_cpp); (p1, a_cpp)], method_ret_ty, stmts)
                    | _ ->
                        let env = snd (push_vars' (List.rev ml_params) (empty_env ())) in
                        let stmts = gen_stmts env (fun x -> Sreturn x) inner_body in
                        (cpp_params, method_ret_ty, stmts)
                  else
                    (* Normal case: we have lambdas - use looked-up return type *)
                    let env = snd (push_vars' (List.rev ml_params) (empty_env ())) in
                    let stmts = gen_stmts env (fun x -> Sreturn x) inner_body in
                    (cpp_params, method_ret_ty, stmts)
                in
                Some (Fmethod (method_name, [], ret_ty, cpp_params, body_stmts, false, true), VPublic)
          in
          (* Zip fields with their types from ind_packet *)
          let fields_with_types =
            if List.length fields = List.length field_types then
              List.combine fields field_types
            else
              (* Fallback: pair fields with Tunknown if lengths don't match *)
              List.map (fun f -> (f, Miniml.Tunknown)) fields
          in
          let method_pairs = List.combine fields_with_types method_bodies in
          let methods = List.filter_map (fun ((fld, fty), body) -> gen_method (fld, fty) body) method_pairs in
          if methods = [] then (None, Some class_ref, type_args)
          else (Some (Dstruct (name, methods)), Some class_ref, type_args)
      | _ -> (None, Some class_ref, type_args))
  | _ -> (None, None, [])

(* Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (body : ml_ast) (ty : ml_type) : bool =
  match ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(* order by index! *)
let get_tvars t =
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
    | Tstruct (_, tys) -> List.fold_left aux l tys
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | _ -> l in
  let l = List.sort (fun (x,_) (y,_) -> Int.compare x y) (aux [] t) in
  List.map snd l

let rec glob_subst_expr (id : GlobRef.t) (e1 : cpp_expr) (e2 : cpp_expr) =
match e2 with
  | CPPglob (id', _) ->
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
  | Sreturn e' -> Sreturn (glob_subst_expr id e e')
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
  | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, tys, List.map (var_subst_expr id e1) args)
  | CPPqualified (e', qid) -> CPPqualified (var_subst_expr id e1 e', qid)
  | _ -> e2

and var_subst_stmt (id : Id.t) (e : cpp_expr) (s : cpp_stmt) =
match s with
  | Sreturn e' -> Sreturn (var_subst_expr id e e')
  | Sasgn (id', ty, e') -> Sasgn (id', ty, var_subst_expr id e e')
  | Sexpr e' -> Sexpr (var_subst_expr id e e')
  | Scustom_case (ty, e', tys, brs, str) -> Scustom_case (ty, var_subst_expr id e e', tys,
    List.map (fun (args, ty, stmts) -> (args, ty, List.map (var_subst_stmt id e) stmts)) brs, str)
  | Sswitch (scrut, ind, brs) -> Sswitch (var_subst_expr id e scrut, ind,
    List.map (fun (ctor, stmts) -> (ctor, List.map (var_subst_stmt id e) stmts)) brs)
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
  | Tstruct (r, tys) -> Tstruct (r, List.map (tvar_subst_type tvars) tys)
  | Tref ty -> Tref (tvar_subst_type tvars ty)
  | Tvariant tys -> Tvariant (List.map (tvar_subst_type tvars) tys)
  | Tshared_ptr ty -> Tshared_ptr (tvar_subst_type tvars ty)
  | Tid (id, tys) -> Tid (id, List.map (tvar_subst_type tvars) tys)
  | Tqualified (ty, id) -> Tqualified (tvar_subst_type tvars ty, id)
  | _ -> ty  (* Tvoid, Tstring, Ttodo, Tunknown, Taxiom *)

let rec tvar_subst_expr (tvars : Id.t list) (e : cpp_expr) : cpp_expr =
  let subst_ty = tvar_subst_type tvars in
  let subst_e = tvar_subst_expr tvars in
  match e with
  | CPPglob (r, tys) -> CPPglob (r, List.map subst_ty tys)
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
  | CPPstruct_id (sid, tys, args) -> CPPstruct_id (sid, List.map subst_ty tys, List.map subst_e args)
  | CPPqualified (e', qid) -> CPPqualified (subst_e e', qid)
  | CPPmk_shared ty -> CPPmk_shared (subst_ty ty)
  | _ -> e  (* CPPvar, CPPvar', CPPvisit, CPPstring, CPPuint, CPPthis, CPPrequires *)

and tvar_subst_stmt (tvars : Id.t list) (s : cpp_stmt) : cpp_stmt =
  let subst_ty = tvar_subst_type tvars in
  let subst_e = tvar_subst_expr tvars in
  let subst_s = tvar_subst_stmt tvars in
  match s with
  | Sreturn e -> Sreturn (subst_e e)
  | Sdecl (id, ty) -> Sdecl (id, subst_ty ty)
  | Sasgn (id, ty_opt, e) -> Sasgn (id, Option.map subst_ty ty_opt, subst_e e)
  | Sexpr e -> Sexpr (subst_e e)
  | Scustom_case (ty, e, tys, brs, str) ->
      Scustom_case (subst_ty ty, subst_e e, List.map subst_ty tys,
        List.map (fun (args, ty, stmts) ->
          (List.map (fun (id, ty) -> (id, subst_ty ty)) args, subst_ty ty, List.map subst_s stmts)) brs,
        str)
  | SreturnVoid -> SreturnVoid
  | Sthrow msg -> Sthrow msg  (* throw statements don't need substitution *)
  | Sswitch (scrut, ind, brs) -> Sswitch (subst_e scrut, ind,
    List.map (fun (ctor, stmts) -> (ctor, List.map subst_s stmts)) brs)
  | Sassert _ as s -> s  (* raw strings don't need type var substitution *)

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
  let missing = List.rev (List.mapi (fun i t -> (Id (Id.of_string ("_x" ^ string_of_int i)), t)) (get_missing mldom ids)) in
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
            let type_arg_cpp = List.map (fun t -> convert_ml_type_to_cpp_type (empty_env ()) [] [] t) type_args in
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
  (* For function signature, use renamed ids but exclude typeclass and void params *)
  let ids = List.filter (fun (_, ty) -> not (Table.is_typeclass_type ty) && not (ml_type_is_void ty)) all_ids in
  (* Convert ML types to C++ types and wrap with const. For shared_ptr, use const ref *)
  let ids = List.map (fun (x, ty) ->
    let cpp_ty = convert_ml_type_to_cpp_type env [] [] ty in
    let wrapped = match cpp_ty with
      | Tshared_ptr _ -> Tref (Tmod (TMconst, cpp_ty))  (* const std::shared_ptr<T>& *)
      | _ -> Tmod (TMconst, cpp_ty)  (* const T *)
    in
    (x, wrapped)) ids in
  let fun_tys = List.filter_map (fun (x, ty, i) ->
      match ty with
      |  (Tmod (TMconst, Tfun (dom, cod))) -> Some (x, TTfun (dom, cod), Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids)) in
  let ids = List.mapi (fun i (x, ty) ->
      match ty with
      |  (Tmod (TMconst, Tfun (dom, cod))) ->
        (x, Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ (string_of_int ((List.length ids) - i - 1))))))))
      | _ -> (x, ty)) ids in
  (* TODO: below is needed for lambdas in recursive positiions, but is badddddd. *)
  (* let rec_fun_tys = List.map (fun (_,t, _) ->
    match t with
    | TTfun (dom, cod) -> Tref (Tmod (TMconst, Tfun (dom, cod)))
    | _ -> assert false) fun_tys in
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps @ rec_fun_tys) in *)
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps) in (* TODO: REMOVE. Hack while we figure out missing type arguments for MLGlob terms when they are given as section variables. NOTE: doesn't work if parameters change in recursive call. *)
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic = List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps in
  let temps = typeclass_temps_basic @ temps @ (List.map (fun (_,t,n) -> (t,n)) fun_tys) in
  (* TODO: Build requires clause for type class constraints
     For now, type class constraints are not enforced at compile time.
     The constraints would use the typeclass_temps info to generate
     requires clauses like: requires Eq<I, T1> *)
  (* let forward_fun_args stmt = List.fold_left (fun s (x, _, fid) ->
    var_subst_stmt x (CPPforward (Tvar (0, Some fid), CPPvar x)) s) stmt fun_tys in *)
  (* Set current type variables for pattern matching lambda generation.
     These are the template parameters that can be used in type annotations. *)
  let type_var_ids = List.filter_map (fun (tt, id) ->
    match tt with TTtypename -> Some id | _ -> None) temps in
  set_current_type_vars type_var_ids;
  set_current_param_types all_ids;
  (* Set the outer function name so inner fixpoints can generate lifted names *)
  let saved_outer_name = !current_outer_function_name in
  current_outer_function_name := Some (Common.pp_global_name Term n);
  (* Check if the return type is coinductive - if so, wrap body in lazy thunk *)
  let rec get_ml_return_type = function
    | Miniml.Tarr (_, t2) -> get_ml_return_type t2
    | t -> t in
  let ml_ret = get_ml_return_type ty in
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
          List.map (fun t -> convert_ml_type_to_cpp_type env [] type_var_ids t) args
        | _ -> [] in
      let lazy_factory = CPPqualified (
        CPPqualified (CPPglob (coind_ref, type_args), Id.of_string "ctor"),
        Id.of_string "lazy_") in
      let thunk = CPPlambda ([], Some ret_cpp,
        [Sreturn x], true) in
      Sreturn (CPPfun_call (lazy_factory, [thunk]))
    else
      Sreturn x in
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

         Then we apply the lifted body to the eta-expansion arguments. *)
      let k = List.length missing in
      let lifted_b = ast_lift k b in
      let args = List.rev (List.mapi (fun i _ -> MLrel (i + 1)) missing) in
      let b = List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap (MLapp (lifted_b, args))) in
      (* let b = List.map forward_fun_args b in *)
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfundef ([n, []], cod, ids, sigma_asserts @ b) in
  current_outer_function_name := saved_outer_name;
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

(* TODO: is this used? Likely, but the template stuff shouldn't be. *)
let gen_sfun n b dom cod temps =
  let ids,b = collect_lams b in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) (empty_env ()) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  (* Convert ML types to C++ types and wrap with const. For shared_ptr, use const ref *)
  let ids = List.map (fun (x, ty) ->
    let cpp_ty = convert_ml_type_to_cpp_type env [] [] ty in
    let wrapped = match cpp_ty with
      | Tshared_ptr _ -> Tref (Tmod (TMconst, cpp_ty))  (* const std::shared_ptr<T>& *)
      | _ -> Tmod (TMconst, cpp_ty)  (* const T *)
    in
    (Some x, wrapped)) ids in
  let dom = List.filter (fun ty -> ty != Tvoid) dom in
  (* For already-converted C++ types in dom, wrap shared_ptr with const ref *)
  let args = List.mapi (fun i ty ->
    let wrapped = match ty with
      | Tshared_ptr _ -> Tref (Tmod (TMconst, ty))  (* const std::shared_ptr<T>& *)
      | _ -> Tmod (TMconst, ty)  (* const T *)
    in
    (None, wrapped)) dom in
  let inner = if List.length args > List.length ids (* TODO: find/fix bug so we don't need this *)
    then Dfundecl ([n, []], cod, List.rev args)
    else Dfundecl ([n, []], cod, ids) in
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

let gen_decl n b ty =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
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
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) ->
    let f, e = gen_dfun n b dom cod ty temps in
  let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
  let tvars = tvars @ fun_tys in
    Some f, e, tvars
  | _ ->
    None, empty_env (), tvars (*
    let inner = Dasgn (n, Tmod (TMconst, ty),  gen_expr (empty_env ()) b) in
    (match temps with
      | [] -> inner, empty_env ()
      | l -> Dtemplate (l, inner), empty_env ())*)

(* TODO: maybe cleanup this function/its name etc.. *)
let gen_decl_for_dfuns n b ty =
  (* Simplify the ML type to resolve metavariables before converting to C++ *)
  let ty = type_simpl ty in
  let b = resolve_body_tvars b ty in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) ->
    let (f, env) = gen_dfun n b dom cod ty temps in
    let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
    let tvars = tvars @ fun_tys in
    f , env , tvars
  | _ -> let (f, env) = gen_dfun n b [Tvoid] cty ty temps in f , env , tvars

let gen_spec n b ty =
  let ty = type_simpl ty in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let temps = List.map (fun id -> (TTtypename, id)) (get_tvars ty) in
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
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let temps = List.map (fun id -> (TTtypename, id)) (get_tvars ty) in
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

let gen_dfuns_header (ns,bs,tys) =
  List.concat_map (fun (i, name) ->
    let (ds, env, tvars) = gen_decl_for_dfuns name bs.(i) tys.(i) in
    let lifted = take_lifted_decls () in
    let lifted_results = List.map (fun d -> (d, empty_env ())) lifted in
    let main_result = match tvars with
      | [] ->
        let b = resolve_body_tvars bs.(i) tys.(i) in
        gen_spec_for_sfuns name b tys.(i)
      | _::_ -> ds, env in
    lifted_results @ [main_result]
  ) (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

let gen_ind_header vars name cnames tys =
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let add_templates d = match templates with
  | [] -> d
  | _ -> Dtemplate (templates, None, d) in
  let header = Array.to_list (Array.map (fun x -> add_templates (Dstruct_decl x)) cnames) in
  let vartydecl = add_templates (Dusing (name , Tvariant (Array.to_list (Array.map (fun x -> Tstruct (x, List.mapi (fun i id -> Tvar (i, Some id)) vars)) cnames)))) in
  let constrdecl = Array.to_list (Array.mapi
    (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) [name] vars x)) tys in
      (* For function parameters, use const ref for shared_ptr types *)
      let constr_params = List.map (fun (x, ty) ->
        let wrapped = match ty with
          | Tshared_ptr _ -> Tref (Tmod (TMconst, ty))  (* const std::shared_ptr<T>& *)
          | _ -> ty
        in
        (x, wrapped)) constr in
      let make_args = List.map(fun (x,_) -> CPPglob (GlobRef.VarRef x, [])) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make_decl = Ffundecl (Id.of_string "make", Tmod (TMstatic, (ind_ty_ptr name ty_vars)), List.rev constr_params) in
      let make_def = Ffundef (Id.of_string "make", Tmod (TMstatic, Tshared_ptr (Tglob (name, ty_vars, []))), constr_params,
        [Sreturn (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)]))]) in
      if ty_vars == []
        then add_templates (Dstruct (c, List.append (List.map (fun (x, y) -> (Fvar (x,y), VPublic)) constr) [make_decl,VPublic]))
        else add_templates (Dstruct (c, List.append (List.map (fun (x, y) -> (Fvar (x,y), VPublic)) constr) [make_def,VPublic])))
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
  let (_all_args, ret_ty) = get_args_and_ret [] ty in

  (* Find extra type variables (beyond the containing type's) *)
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let extra_tvars = List.filter (fun i -> i < 1 || i > num_ind_vars) all_tvars in
  let extra_tvar_names = List.map (fun i -> Id.of_string ("T" ^ string_of_int i)) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars num_ind_vars extra_tvar_map in

  (* Convert return type *)
  let ret_cpp = convert_ml_type_to_cpp_type (empty_env ()) [name] vars ret_ty in
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

  (* Extract 'this' argument at this_pos - use renamed ids for consistency with body *)
  let ids_normal_order = List.rev all_ids in
  let (this_arg_id_opt, param_ids) = Common.extract_at_pos this_pos
    (List.map (fun (id, ty) -> (id, ty)) ids_normal_order) in
  let this_arg_id = Option.map fst this_arg_id_opt in
  let param_ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) param_ids in

  (* Convert params to C++ types *)
  let params_with_idx = List.mapi (fun i (id, ty) ->
    let cpp_ty = convert_ml_type_to_cpp_type env [name] vars ty in
    let cpp_ty = subst_extra_tvars cpp_ty in
    (id, cpp_ty, i)
  ) param_ids in

  (* Extract function-typed parameters for template params *)
  let fun_params = List.filter_map (fun (id, cpp_ty, i) ->
    match cpp_ty with
    | Tfun (dom, cod) -> Some (id, TTfun (dom, cod), Id.of_string ("F" ^ string_of_int i))
    | _ -> None
  ) params_with_idx in

  (* Build template params *)
  let extra_type_params = List.map (fun name -> (TTtypename, name)) extra_tvar_names in
  let fun_template_params = List.map (fun (_, tt, fname) -> (tt, fname)) fun_params in
  let template_params = extra_type_params @ fun_template_params in

  (* Build final params with proper wrapping *)
  let params = List.map (fun (id, cpp_ty, i) ->
    let wrapped = match cpp_ty with
      | Tfun _ -> Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ string_of_int i)))))
      | Tshared_ptr _ -> Tref (Tmod (TMconst, cpp_ty))
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
          List.map (fun t -> convert_ml_type_to_cpp_type (empty_env ()) [name] vars t) args
        | _ -> [] in
      let coind_ref = match ret_ty with
        | Miniml.Tglob (r, _, _) -> r
        | _ -> assert false in
      let lazy_factory = CPPqualified (
        CPPqualified (CPPglob (coind_ref, type_args), Id.of_string "ctor"),
        Id.of_string "lazy_") in
      let thunk = CPPlambda ([], Some ret_cpp,
        [Sreturn x], true) in
      Sreturn (CPPfun_call (lazy_factory, [thunk]))
    else
      Sreturn x in
  (* Generate method body *)
  let stmts = gen_stmts env method_k inner_body in
  let stmts = match this_arg_id with
    | Some id -> List.map (var_subst_stmt id CPPthis) stmts
    | None -> stmts
  in
  let stmts = List.map (tvar_subst_stmt vars) stmts in

  (Fmethod (func_name, template_params, ret_cpp, params, stmts, true, false), VPublic)

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
  let add_templates d = match templates with
    | [] -> d
    | _ -> Dtemplate (templates, None, d) in

  (* Handle empty inductives (no constructors) - generate uninhabitable struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate:
       struct empty {
         empty() = delete;
       };
       This type cannot be constructed, matching the semantics of empty types. *)
    let method_fields = List.map (gen_single_method name vars) method_candidates in
    add_templates (Dstruct (name, [(Fdeleted_ctor, VPublic)] @ method_fields))
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
    Denum (name, ctor_names)
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
        let cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) [name] vars ty in
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

  (* 5. Public ctor struct with factory methods *)
  let factory_methods = Array.to_list (Array.mapi
    (fun i tys_list ->
      let c = cnames.(i) in
      let cname = match c with
        | GlobRef.ConstructRef _ -> Common.pp_global_name Type c
        | _ -> "Ctor" ^ string_of_int i
      in
      let factory_name = Id.of_string (cname ^ "_") in
      (* Parameters - use const ref for shared_ptr types *)
      let params = List.mapi (fun j ty ->
        let cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) [name] vars ty in
        (* For indexed inductives (no template params), erase unnamed Tvars to std::any *)
        let cpp_ty = if vars = [] then tvar_erase_type cpp_ty else cpp_ty in
        let wrapped = match cpp_ty with
          | Tshared_ptr _ -> Tref (Tmod (TMconst, cpp_ty))  (* const std::shared_ptr<T>& *)
          | _ -> cpp_ty
        in
        (Id.of_string ("a" ^ string_of_int j), wrapped)
      ) tys_list in
      (* Constructor arguments: use params to build the alternative struct *)
      let ctor_args = List.mapi (fun j _ ->
        CPPvar (Id.of_string ("a" ^ string_of_int j))
      ) tys_list in
      (* Body: return std::shared_ptr<Tree>(new Tree(Ctor{args})) *)
      (* Note: nested struct types don't need template args - they inherit from parent *)
      let ctor_struct = CPPstruct_id (Id.of_string cname, [], ctor_args) in
      let new_expr = CPPnew (Tglob (name, ty_vars, []), [ctor_struct]) in
      let shared_ptr_expr = CPPshared_ptr_ctor (Tglob (name, ty_vars, []), new_expr) in
      let body = [Sreturn shared_ptr_expr] in
      (Ffundef (factory_name, Tmod (TMstatic, self_ty), params, body), VPublic)
    ) tys) in

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
       Sreturn (CPPfun_call (CPPvar (Id.of_string_soft "std::move"),
         [CPPfun_call (CPPvar (Id.of_string_soft "const_cast<variant_t&>"),
           [CPPmethod_call (CPPvar (Id.of_string "_tmp"), Id.of_string "v", [])])]))]
      , true) in
    let new_expr = CPPnew (Tglob (name, ty_vars, []),
      [CPPfun_call (CPPvar (Id.of_string_soft "std::function<variant_t()>"),
        [adapter_lambda])]) in
    let shared_ptr_expr = CPPshared_ptr_ctor (Tglob (name, ty_vars, []), new_expr) in
    let body = [Sreturn shared_ptr_expr] in
    [(Ffundef (lazy_name, Tmod (TMstatic, self_ty), params, body), VPublic)]
  else [] in

  (* Add deleted default constructor to ctor struct *)
  let ctor_struct_fields = (Fdeleted_ctor, VPublic) :: factory_methods @ lazy_factory in
  let ctor_struct = (Fnested_struct (Id.of_string "ctor", ctor_struct_fields), VPublic) in

  (* Add public accessor for v_ to enable pattern matching from outside *)
  let v_accessor = if is_coinductive then
    (* For coinductive: const variant_t& v() const { return lazy_v_.force(); } *)
    (Fmethod (
      Id.of_string "v",
      [],
      Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", []))),
      [],
      [Sreturn (CPPfun_call (CPPmember (CPPvar (Id.of_string "lazy_v_"), Id.of_string "force"), []))],
      true,
      false
    ), VPublic)
  else
    (* For inductive: const variant_t& v() const { return v_; } *)
    (Fmethod (
      Id.of_string "v",
      [],
      Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", []))),
      [],
      [Sreturn (CPPvar (Id.of_string "v_"))],
      true,
      false
    ), VPublic) in

  (* 6. Generate methods from method candidates using shared helper *)
  let method_fields = List.map (gen_single_method name vars) method_candidates in

  (* Combine all fields in order:
     - Constructor structs (public)
     - variant_t using (public)
     - v_ member (private)
     - Private constructors
     - ctor struct (public)
     - v() accessor (public)
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
    method_fields
  in

  (* Just the struct itself - no extra namespace wrapper *)
  add_templates (Dstruct (name, all_fields))

(* Generate methods for eponymous records.
   Uses the shared gen_single_method helper for records where methods are
   generated directly on the module struct (which has record fields merged).
   name: the record's GlobRef (e.g., IndRef for CHT)
   vars: the type variables of the record (e.g., [K; V] for CHT<K, V>)
   method_candidates: list of (func_ref, body, type, this_position) tuples *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  List.map (gen_single_method name vars) method_candidates
