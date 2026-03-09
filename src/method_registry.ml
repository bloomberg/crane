(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Method registry: pre-scans the full extraction structure to identify
   which functions should become methods on eponymous inductive types.

   This module is the first pass in Crane's multi-pass extraction pipeline.
   It runs before any C++ code is emitted, building a table that maps
   function GlobRef.t values to their method_info records.

   The overall flow is:
     1. [create] iterates every module in the ml_structure.
     2. For each module, it finds the eponymous inductive (if any) —
        the inductive whose lowercase name matches the module name.
     3. For each function in that module (and wrapper modules), it checks
        whether the function's type has the eponymous type as an argument.
     4. It verifies the function body is safe (no bare [return this]).
     5. After all methods are found, [compute_returns_any] checks which
        methods have return types that need to be erased to [std::any].

   See method_registry.mli for the full interface documentation. *)

open Util
open Names
open Table
open Miniml
open Common

type method_info = {
  epon_ref : GlobRef.t;
  this_pos : int;
  ind_tvar_positions : int list;
  returns_any : bool;
}

type method_candidate = GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int

type t = {
  methods : (GlobRef.t, method_info) Hashtbl.t;
  (* Reverse index: inductive GlobRef -> list of method candidates.
     Populated during pre-scan so cpp.ml doesn't need to re-collect. *)
  candidates : (GlobRef.t, method_candidate list) Hashtbl.t;
}

(* ------------------------------------------------------------------ *)
(* Body safety check                                                   *)
(* ------------------------------------------------------------------ *)

(* Check if a function body is safe to turn into a method.

   Background: when a function becomes a C++ method, its first argument
   is received via the [this] pointer (a raw pointer) rather than as a
   [std::shared_ptr].  If the function's body directly returns that first
   argument (a bare [MLrel] in tail position), the generated C++ would
   produce [return this;] — but [this] is a raw pointer and cannot be
   implicitly converted back to [std::shared_ptr<T>], causing a
   compilation error.

   This function returns [true] if the body is safe to transform.

   Note: we only check for DIRECT returns of the first argument.  Using
   the first argument for field access (record projection), match
   dispatch, or passing to other methods is fine — those translate to
   [this->field], [this->v()], and [this->method()] respectively, none
   of which require converting [this] back to [shared_ptr].

   The check works by:
   1. Stripping outer lambdas to find the inner body and computing the
      de Bruijn index of the first argument.
   2. Recursing through tail positions (match branches, let bodies,
      fixpoint bodies, MLmagic wrappers) to see if any tail position
      is a bare [MLrel] pointing at the first argument.
   3. Special-casing top-level matches on the first argument (common
      pattern for destructors) — only the branches are checked, not
      the scrutinee itself (which is obviously the first argument but
      is used for dispatch, not returned). *)
let body_safe_for_method body =
  (* Strip outer lambdas, counting them.  The number of lambdas tells us
     the de Bruijn index of the outermost (first) argument: in
     [fun a b c -> body], argument [a] has index 3 inside [body]. *)
  let rec strip_lams n = function
    | MLlam (_, _, b) -> strip_lams (n + 1) b
    | b -> (n, b)
  in
  let (num_lams, inner) = strip_lams 0 body in
  (* The first argument (position 0) has de Bruijn index = num_lams
     because de Bruijn indices count from the innermost binder outward. *)
  let target_db = num_lams in
  (* Check if [MLrel target_db] appears as a direct return value in the
     AST.  A "direct return" means the expression IS just [MLrel] (not
     wrapped in [MLapp], [MLcons], etc.).  We recurse through match
     branches, let bodies, and fixpoints to find all result positions.

     [depth] tracks additional binders introduced inside the body
     (e.g. match branch bindings, let bindings) that shift the de Bruijn
     index of the target argument. *)
  let rec returns_target depth = function
    | MLrel i -> i = target_db + depth
    | MLcase (_, _scrut, branches) ->
      Array.exists (fun (ids, _, _, branch_body) ->
        let n_bindings = List.length ids in
        returns_target (depth + n_bindings) branch_body
      ) branches
    | MLletin (_, _, _, b) -> returns_target (depth + 1) b
    | MLmagic a -> returns_target depth a
    (* All other forms (MLapp, MLcons, MLlam, etc.) produce a NEW value,
       not a bare return of the argument. So they're safe. *)
    | _ -> false
  in
  (* Check the inner body.  Three cases: *)
  match inner with
  | MLcase (_, MLrel scrut_idx, branches) when scrut_idx = target_db ->
    (* Case 1: Top-level match on first arg (e.g. [match xs with ...]).
       Only check branches, not the scrutinee — the scrutinee is the
       first argument but is used for dispatch, not directly returned. *)
    not (Array.exists (fun (ids, _, _, branch_body) ->
      let n_bindings = List.length ids in
      returns_target n_bindings branch_body
    ) branches)
  | MLfix (fix_idx, _, funs, _) ->
    (* Case 2: Top-level fixpoint (recursive function).  Check the body
       of the fixpoint at [fix_idx].  The fixpoint array introduces
       [n_funs] additional binders (the mutually recursive functions). *)
    let n_funs = Array.length funs in
    let fix_body = funs.(fix_idx) in
    let (fix_lams, fix_inner) = strip_lams 0 fix_body in
    let fix_target_db = target_db + n_funs + fix_lams in
    (match fix_inner with
     | MLcase (_, MLrel scrut_idx, branches) when scrut_idx = fix_target_db ->
       not (Array.exists (fun (ids, _, _, branch_body) ->
         let n_bindings = List.length ids in
         returns_target (n_funs + fix_lams + n_bindings) branch_body
       ) branches)
     | _ -> not (returns_target n_funs fix_body))
  | _ ->
    (* Case 3: Any other body shape — check if the target appears in
       any tail position. *)
    not (returns_target 0 inner)

(* ------------------------------------------------------------------ *)
(* Eponymous-type helpers                                              *)
(* ------------------------------------------------------------------ *)

(* Find the eponymous inductive in a module's declarations.

   An inductive is "eponymous" when its lowercase name matches the module
   name (also lowercased).  For example, module [List] has eponymous
   inductive [list], module [Nat] has eponymous inductive [nat].

   Type-class inductives are excluded because they become C++ concepts
   rather than structs, so attaching methods to them does not apply.

   Only searches [SEdecl (Dind ...)] entries at the current level;
   does not recurse into sub-modules. *)
let find_eponymous_inductive module_name_str decls =
  let lowercase_module = String.lowercase_ascii module_name_str in
  List.find_map (fun (_l, se) ->
    match se with
    | SEdecl (Dind (kn, ind)) ->
      (* A single Dind may have multiple packets (mutual inductives).
         Check each packet's name against the module name. *)
      let rec find_in_packets i =
        if i >= Array.length ind.ind_packets then None
        else
          let _p = ind.ind_packets.(i) in
          let ind_ref = GlobRef.IndRef (kn, i) in
          let ind_name = Common.pp_global_name Type ind_ref in
          if String.lowercase_ascii ind_name = lowercase_module then
            match ind.ind_kind with
            | TypeClass _ -> None  (* Type classes become concepts, not methods *)
            | Record _ -> Some ind_ref  (* Eponymous record *)
            | _ -> Some ind_ref  (* Eponymous inductive *)
          else find_in_packets (i + 1)
      in
      find_in_packets 0
    | _ -> None
  ) decls

(* Find the position of the first argument matching an eponymous type.

   Walks the curried arrow type [T1 -> T2 -> ... -> Tn -> R], checking
   each [Ti] to see if it is [Tglob(epon_ref, tvar_args, _)].

   Returns [Some (pos, ind_tvar_positions)] where:
   - [pos] is the 0-based argument index that will become [this].
   - [ind_tvar_positions] lists which of the function's type variables
     are used as type parameters of the inductive at that argument
     position.  These are already deducible from the receiver type and
     can be omitted from the method's template parameters.

   Example: for [app : forall A, list A -> list A -> list A]:
   - The type is [Tarr(Tglob(list, [Tvar 1], _), Tarr(..., ...))].
   - [Tglob]'s first arg matches [epon_ref], so [pos = 0].
   - [tvar_args = [Tvar 1]], so [ind_tvar_positions = [0]] (Tvar 1 maps
     to 0-based index 0 in the type parameter list). *)
let find_epon_arg_pos epon_ref ty =
  let rec aux pos = function
    | Miniml.Tarr (Miniml.Tglob (arg_ref, tvar_args, _), rest)
      when Environ.QGlobRef.equal Environ.empty_env arg_ref epon_ref ->
      let ind_tvar_positions = List.filter_map (fun t ->
        match t with
        | Miniml.Tvar i | Miniml.Tvar' i -> Some (i - 1)
        | _ -> None
      ) tvar_args in
      Some (pos, ind_tvar_positions)
    | Miniml.Tarr (_, rest) -> aux (pos + 1) rest
    | _ -> None
  in
  aux 0 ty

(* ------------------------------------------------------------------ *)
(* Internal: registration helpers                                      *)
(* ------------------------------------------------------------------ *)

(* Add a method entry to the hashtable.  [returns_any] is initialized to
   [false] and computed in a separate pass after all methods are found. *)
let register_into tbl (func_ref : GlobRef.t) (epon_ref : GlobRef.t) (this_pos : int) ~(ind_tvar_positions : int list) =
  Hashtbl.replace tbl func_ref {
    epon_ref;
    this_pos;
    ind_tvar_positions;
    returns_any = false;  (* computed later by [compute_returns_any] *)
  }

(* Register all eligible methods for a given eponymous type from a list
   of declarations.

   A function is eligible if:
   1. It is in the same module as the eponymous type (or in a wrapper
      module, or [~cross_module:true] is set).
   2. Its body passes [body_safe_for_method].
   3. Its type has the eponymous type as an argument (found by
      [find_epon_arg_pos]).

   Module matching:
   - [~cross_module:false] (default): only functions in the same
     [ModPath] as the eponymous type are considered.
   - [~wrapper_module_name:Some name]: also allows functions from modules
     whose last path component matches [name] (case-insensitive, prefix
     match).  This handles "wrapper modules" where e.g. module [ListAux]
     contains additional functions for [list].
   - [~cross_module:true]: allows any module.  Used when registering
     methods from parent-level declarations that reference the eponymous
     type.

   Custom types and enum-only inductives are excluded — custom types have
   user-provided C++ implementations, and enums are rendered as [enum class]
   values with no struct to attach methods to. *)
let register_methods_for_epon tbl cands ?(cross_module=false) ?(wrapper_module_name : string option = None) epon_ref decls =
  if is_custom epon_ref || Table.is_enum_inductive epon_ref then ()
  else
  let epon_modpath = modpath_of_r epon_ref in
  (* Check if a function reference [r] comes from a wrapper module. *)
  let from_wrapper_module r =
    match wrapper_module_name with
    | None -> false
    | Some name ->
      let func_mp = modpath_of_r r in
      let lc_name = String.lowercase_ascii name in
      (* Prefix match: "listaux" starts with "list" *)
      let name_matches mp_name =
        mp_name = lc_name ||
        (String.length mp_name > String.length lc_name &&
         String.sub mp_name 0 (String.length lc_name) = lc_name)
      in
      match func_mp with
      | MPdot (_, lbl) ->
        name_matches (String.lowercase_ascii (Label.to_string lbl))
      | MPfile dp ->
        (match DirPath.repr dp with
         | id :: _ -> name_matches (String.lowercase_ascii (Id.to_string id))
         | [] -> false)
      | _ -> false
  in
  let same_module r = cross_module || from_wrapper_module r || ModPath.equal (modpath_of_r r) epon_modpath in
  (* Helper to add a candidate to both the method table and candidates table *)
  let add_candidate r body ty pos ind_tvar_positions =
    register_into tbl r epon_ref pos ~ind_tvar_positions;
    let existing = match Hashtbl.find_opt cands epon_ref with
      | Some l -> l | None -> []
    in
    Hashtbl.replace cands epon_ref (existing @ [(r, body, ty, pos)])
  in
  List.iter (fun (_l, se) ->
    match se with
    | SEdecl (Dterm (r, body, ty)) ->
      if same_module r then
        (match find_epon_arg_pos epon_ref ty with
         | Some (pos, ind_tvar_positions) ->
           add_candidate r body ty pos ind_tvar_positions
         | None -> ())
    | SEdecl (Dfix (rv, defs, typs)) ->
      (* Mutual fixpoints: check each function in the fixpoint block. *)
      Array.iteri (fun i r ->
        if same_module r then
          match find_epon_arg_pos epon_ref typs.(i) with
          | Some (pos, ind_tvar_positions) ->
            add_candidate r defs.(i) typs.(i) pos ind_tvar_positions
          | None -> ()
      ) rv
    | _ -> ()
  ) decls

(* ------------------------------------------------------------------ *)
(* Pre-registration pass                                               *)
(* ------------------------------------------------------------------ *)

(* Pre-register all methods from the entire structure before code
   generation.  This ensures that cross-module method calls (like
   [List.app] called from a different module) are recognized correctly
   during code generation.

   The scan has two levels of behavior controlled by [~at_top_level]:

   {b Top level} ([at_top_level = true]):
   For inductives at the actual top level of the extraction (e.g.
   stdlib's [list] which lives at file scope, not inside a module),
   sibling functions in the same file-level declarations are checked
   as method candidates.  Additionally, functions in parent-level
   declarations that match a wrapper module naming pattern are also
   registered.

   {b Inside modules} ([at_top_level = false]):
   For inductives inside a [SEmodule], the standard eponymous type
   detection applies: the module name is compared against inductive names,
   and functions within that module are checked.

   Both levels perform early enum detection (needed so that
   [register_methods_for_epon] can skip enum types), then recurse
   into sub-modules.

   [parent_decls] accumulates declarations from enclosing scopes,
   enabling cross-module method registration (e.g. a function in an
   outer module that takes an inner module's eponymous type). *)
let rec pre_register_methods_from_structure tbl cands ~at_top_level (parent_decls : (Label.t * Miniml.ml_structure_elem) list) (sel : (Label.t * Miniml.ml_structure_elem) list) : unit =
  (* Handle top-level inductives that may have sibling methods. *)
  if at_top_level then
    List.iter (fun (_l, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        let is_mutual = Array.length ind.ind_packets > 1 in
        Array.iteri (fun i p ->
          let ind_ref = GlobRef.IndRef (kn, i) in
          (* Early enum detection: we need to know which inductives are
             enums before trying to register methods, because enum types
             should not have methods attached. *)
          if not (is_custom ind_ref) && not is_mutual then begin
            let all_nullary = Array.for_all (fun tys_list -> tys_list = []) p.ip_types in
            let param_sign = List.firstn ind.ind_nparams p.ip_sign in
            let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
            if all_nullary && num_param_vars = 0 && Array.length p.ip_types > 0 then
              Table.add_enum_inductive ind_ref
          end;
          (* Skip type classes — they become C++ concepts, not structs. *)
          (match ind.ind_kind with
           | TypeClass _ -> ()
           | _ ->
             (* Register methods from sibling declarations at this level. *)
             register_methods_for_epon tbl cands ind_ref sel;
             (* Also check parent-level declarations for wrapper module
                functions (e.g. [ListAux.foo] taking a [list] argument). *)
             let ind_name = Common.pp_global_name Type ind_ref in
             register_methods_for_epon tbl cands ~wrapper_module_name:(Some ind_name) ind_ref parent_decls)
        ) ind.ind_packets
      | _ -> ()
    ) sel;
  (* Process each declaration, recursing into sub-modules. *)
  List.iter (fun (l, se) ->
    match se with
    | SEmodule m ->
      (match m.ml_mod_expr with
       | MEstruct (_mp, inner_sel) ->
         (* Early enum detection for inductives inside this module. *)
         List.iter (fun (_l', se') ->
           match se' with
           | SEdecl (Dind (kn', ind')) ->
             let is_mutual' = Array.length ind'.ind_packets > 1 in
             Array.iteri (fun i' p' ->
               let ind_ref' = GlobRef.IndRef (kn', i') in
               if not (is_custom ind_ref') && not is_mutual' then begin
                 let all_nullary = Array.for_all (fun tys_list -> tys_list = []) p'.ip_types in
                 let param_sign = List.firstn ind'.ind_nparams p'.ip_sign in
                 let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
                 if all_nullary && num_param_vars = 0 && Array.length p'.ip_types > 0 then
                   Table.add_enum_inductive ind_ref'
               end
             ) ind'.ind_packets
           | _ -> ()
         ) inner_sel;
         (* Check for an eponymous inductive inside this module.
            E.g. module [List] contains inductive [list]. *)
         let module_name_str = Label.to_string l in
         (match find_eponymous_inductive module_name_str inner_sel with
          | Some epon_ref ->
            (* Register methods from within the module. *)
            register_methods_for_epon tbl cands epon_ref inner_sel;
            (* Also register cross-module methods: functions in parent
               declarations whose module name starts with the eponymous
               type name. *)
            register_methods_for_epon tbl cands ~cross_module:true
              ~wrapper_module_name:(Some module_name_str) epon_ref parent_decls
          | None -> ());
         (* Recurse into the module's contents.  Accumulate current-level
            declarations into [parent_decls] for nested modules. *)
         pre_register_methods_from_structure tbl cands ~at_top_level:false (parent_decls @ sel) inner_sel
       | MEfunctor (_mbid, _mt, body) ->
         (* Recurse into functor bodies — they may contain modules with
            eponymous types. *)
         pre_register_methods_from_module_expr tbl cands (parent_decls @ sel) body
       | _ -> ())
    | _ -> ()
  ) sel

(* Recurse into module expressions (struct bodies and functor bodies)
   to find nested modules with eponymous types. *)
and pre_register_methods_from_module_expr tbl cands (parent_decls : (Label.t * Miniml.ml_structure_elem) list) = function
  | MEstruct (_mp, sel) ->
    pre_register_methods_from_structure tbl cands ~at_top_level:false parent_decls sel
  | MEfunctor (_mbid, _mt, body) ->
    pre_register_methods_from_module_expr tbl cands parent_decls body
  | _ -> ()

(* ------------------------------------------------------------------ *)
(* Compute returns_any for all registered methods                      *)
(* ------------------------------------------------------------------ *)

(* After the full structure has been scanned for methods, determine which
   methods return [std::any] (erased indexed return types).

   In C++, when an inductive type has type parameters, those parameters
   become template parameters on the struct.  If a method's return type
   involves a type variable that is NOT one of the inductive's parameters
   (i.e. it is an "indexed" type variable), it cannot be expressed in the
   C++ type system and must be erased to [std::any].

   For example, consider:
     [Inductive Foo (A : Type) := mk : A -> Foo A.]
     [Definition bar (A B : Type) (x : Foo A) : B := ...]
   Here [B] is not a parameter of [Foo], so [bar]'s return type is
   erased to [std::any] in the method signature.

   The algorithm:
   1. Build a mapping from each inductive [GlobRef] to its parameter
      variable names (the [ip_vars] that correspond to kept parameters).
   2. For each registered method, find its ML type in the structure,
      extract the return type, convert it to a MiniCpp type, and check
      if [Translation.type_is_erased] reports it as erased.
   3. If erased, set [returns_any = true] in the method's entry. *)
let compute_returns_any tbl (s : ml_structure) =
  (* Step 1: Build mapping from IndRef -> param_vars for all inductives. *)
  let ind_param_vars : (GlobRef.t, Id.t list) Hashtbl.t = Hashtbl.create 32 in
  let rec collect_from_sel sel =
    List.iter (fun (_l, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        Array.iteri (fun i p ->
          let ind_ref = GlobRef.IndRef (kn, i) in
          let param_sign = List.firstn ind.ind_nparams p.ip_sign in
          let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
          let param_vars = List.firstn num_param_vars p.ip_vars in
          Hashtbl.replace ind_param_vars ind_ref param_vars
        ) ind.ind_packets
      | SEmodule m ->
        (match m.ml_mod_expr with
         | MEstruct (_mp, inner_sel) -> collect_from_sel inner_sel
         | _ -> ())
      | _ -> ()
    ) sel
  in
  List.iter (fun (_mp, sel) -> collect_from_sel sel) s;
  (* Step 2: For each registered method, find its ML type and check
     whether the return type is erased. *)
  Hashtbl.iter (fun func_ref info ->
    match Hashtbl.find_opt ind_param_vars info.epon_ref with
    | None -> ()
    | Some param_vars ->
      (* Extract the return type from a curried arrow type. *)
      let rec get_return_type = function
        | Miniml.Tarr (_, t2) -> get_return_type t2
        | ret -> ret
      in
      (* Search the entire structure for this method's ML type.
         We need the original ML type to convert it to MiniCpp and
         check for erasure. *)
      let find_method_type () =
        let result = ref None in
        let rec search_sel sel =
          List.iter (fun (_l, se) ->
            match se with
            | SEdecl (Dterm (r, _, ty))
              when Environ.QGlobRef.equal Environ.empty_env r func_ref ->
              result := Some ty
            | SEdecl (Dfix (rv, _, typs)) ->
              Array.iteri (fun i r ->
                if Environ.QGlobRef.equal Environ.empty_env r func_ref then
                  result := Some typs.(i)
              ) rv
            | SEmodule m ->
              (match m.ml_mod_expr with
               | MEstruct (_mp, inner_sel) -> search_sel inner_sel
               | _ -> ())
            | _ -> ()
          ) sel
        in
        List.iter (fun (_mp, sel) -> search_sel sel) s;
        !result
      in
      (* Step 3: Convert return type to MiniCpp and check for erasure. *)
      (match find_method_type () with
       | None -> ()
       | Some ty ->
         let ret_ml = get_return_type ty in
         let env = empty_env () in
         let ret_cpp = Translation.convert_ml_type_to_cpp_type env Refset'.empty param_vars ret_ml in
         if Translation.type_is_erased ret_cpp then
           Hashtbl.replace tbl func_ref { info with returns_any = true })
  ) tbl

(* ------------------------------------------------------------------ *)
(* Public API                                                          *)
(* ------------------------------------------------------------------ *)

(* Build the complete method registry from the full extraction structure.

   This is the main entry point, called once from [cpp.ml] at the start
   of [do_struct_with_decl_tracking] before any C++ code is rendered.

   The two-phase approach (register methods, then compute returns_any)
   is necessary because [compute_returns_any] needs the full set of
   registered methods and all inductives' parameter information to work
   correctly. *)
let create (s : ml_structure) : t =
  let tbl = Hashtbl.create 100 in
  let cands = Hashtbl.create 32 in
  (* Gather all top-level declarations across all modules.  These serve as
     [parent_decls] for the recursive scan, enabling cross-module method
     detection (e.g. a function at file scope that takes a type from a
     sub-module as its argument). *)
  let all_top_level_decls = List.concat_map snd s in
  List.iter (fun (_mp, sel) ->
    pre_register_methods_from_structure tbl cands ~at_top_level:true all_top_level_decls sel
  ) s;
  compute_returns_any tbl s;
  { methods = tbl; candidates = cands }

let lookup (reg : t) (func_ref : GlobRef.t) : method_info option =
  Hashtbl.find_opt reg.methods func_ref

let is_registered_method (reg : t) (func_ref : GlobRef.t) : (GlobRef.t * int) option =
  match Hashtbl.find_opt reg.methods func_ref with
  | Some info -> Some (info.epon_ref, info.this_pos)
  | None -> None

let lookup_ind_tvar_positions (reg : t) (func_ref : GlobRef.t) : int list =
  match Hashtbl.find_opt reg.methods func_ref with
  | Some info -> info.ind_tvar_positions
  | None -> []

let method_returns_any (reg : t) (func_ref : GlobRef.t) : bool =
  match Hashtbl.find_opt reg.methods func_ref with
  | Some info -> info.returns_any
  | None -> false

let get_candidates (reg : t) (ind_ref : GlobRef.t) : method_candidate list =
  match Hashtbl.find_opt reg.candidates ind_ref with
  | Some l -> l
  | None -> []

let register_method (reg : t) (func_ref : GlobRef.t) (epon_ref : GlobRef.t) (this_pos : int) ~(ind_tvar_positions : int list) =
  register_into reg.methods func_ref epon_ref this_pos ~ind_tvar_positions

let add_candidate (reg : t) (ind_ref : GlobRef.t) (cand : method_candidate) =
  let existing = match Hashtbl.find_opt reg.candidates ind_ref with
    | Some l -> l | None -> []
  in
  Hashtbl.replace reg.candidates ind_ref (existing @ [cand])

let register_method_returns_any (reg : t) (func_ref : GlobRef.t) =
  match Hashtbl.find_opt reg.methods func_ref with
  | Some info ->
    Hashtbl.replace reg.methods func_ref { info with returns_any = true }
  | None -> ()
