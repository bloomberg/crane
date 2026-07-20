(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Shared mutable state for the MiniML -> MiniCpp translation.

    Holds the per-declaration translation context ([tctx]) and the module-scope
    [local_inductives] list, plus their accessors, so that the translation core
    ([translation.ml]) and the declaration generators can share this state
    without a dependency cycle.  Mirrors the [cpp_state.ml] pattern used by the
    pretty-printer. *)

module IntMap = Map.Make (Int)

open Common
open Miniml
open Minicpp
open Names
open Table

let local_inductives : GlobRef.t list ref = ref []

(** Register an inductive as local to the current module scope. *)
let add_local_inductive (r : GlobRef.t) =
  local_inductives := r :: !local_inductives

(** Clear the local inductives list (called at module boundaries). *)
let clear_local_inductives () = local_inductives := []

(** Return the list of inductives local to the current module scope. *)
let get_local_inductives () = !local_inductives

(** Helper to create CPPglob with pre-computed custom_info *)
let mk_cppglob (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  let ci =
    {
      ci_inline = (if Table.to_inline r then Table.find_custom_opt r else None);
      ci_is_custom = Table.is_custom r;
    }
  in
  CPPglob (r, tys, Some ci)

(** Helper for local variables (VarRef) - no custom extraction applies *)
let mk_cppglob_local (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  CPPglob (r, tys, None)

(** Safe wrappers for Table lookups that may fail *)
let find_type_opt (r : GlobRef.t) : ml_type option =
  try Some (Table.find_type r) with Not_found -> None

(** Consolidated mutable state for expression compilation.
    All fields except {!local_inductives} (which has a different lifecycle
    and is exported to [cpp.ml]) live here. *)
type translation_ctx = {
  (* Template type variables for the function currently being translated. *)
  mutable current_type_vars : Id.t list;
  (* 1-indexed parameter types for the current function; used to recover
     erased type info at call sites. *)
  mutable current_param_types : (int * ml_type) list;
  (* Name of the enclosing function, for diagnostic messages. *)
  mutable current_outer_function_name : string option;
  (* C++ return type of the enclosing function, set by gen_dfun. Used to
     recover erased template type args at call sites where C++ can't deduce
     them from lambda arguments. *)
  mutable current_cpp_return_type : cpp_type option;
  (* De Bruijn environment mapping variable indices to ML types. *)
  mutable env_types : (Id.t * ml_type) list;
  (* Declarations to be lifted to the enclosing scope (hoisted fixpoints). *)
  mutable pending_lifted_decls : cpp_decl list;
  (* Nesting depth of let ... in expressions; used for unique name
     generation in nested scopes. *)
  mutable current_letin_depth : int;
  (* Escape analysis results: variables whose values are consumed (moved)
     exactly once, so they can be std::move'd. *)
  mutable move_owned_vars : Escape.IntSet.t;
  (* Variables that are dead after this point (last use was in a move). *)
  mutable move_dead_after : Escape.IntSet.t;
  (* When true, suppress tail-position moves (the caller handles them). *)
  mutable move_suppress_tail : bool;
  (* Number of function parameters (offset for de Bruijn indices). *)
  mutable move_n_params : int;
  (* Counter for generating unique match scrutinee variable names
     (_mp0, _mp1, ...). Reset at function boundaries. *)
  mutable match_param_counter : int;
  (* Maps promoted record fields to their C++ qualified types.
     Example: "m_carrier" -> Tqualified(Tvar "_tcI0", "m_carrier")
     (prints as: typename _tcI0::m_carrier).
     Set by gen_dfun when generating template functions with typeclass
     parameters. Used by convert_ml_type_to_cpp_type to resolve
     Tvar(1000, name) markers. *)
  mutable promoted_var_map : (Id.t * cpp_type) list;
  (* When true, we are inside a constructor expression (module-level static
     initializer). Promoted type vars that can't be resolved via
     promoted_var_map fall back to Tany (std::any) instead of keeping
     Tvar(1000, name) markers, because module-level aliases apply. *)
  mutable in_constructor_expr : bool;
  (* ITree extraction mode: controls whether itree types are erased
     (Sequential) or preserved as shared_ptr<ITree<R>> (Reified). *)
  mutable itree_mode : itree_extraction_mode;
  (* When true, eta_fun keeps CPPmove wrappers on captured args and uses
     [&] capture instead of [=]. Set by the MLletin handler when the bound
     variable is used at most once and does not escape. *)
  mutable eta_keep_moves : bool;
  (* Counter for generating unique _cs / _cs1 / _cs2 cache variable names
     for Scustom_case scrutinee caching. Reset at function boundaries. *)
  mutable cs_counter : int;
  (* When generating a method body, holds the set of self-references
     (the inductive type(s) this method belongs to). Merged into the ns
     argument of convert_ml_type_to_cpp_type so that self-refs inside
     container types (e.g. List<tree>) get shared_ptr wrapping, matching
     the struct definition. Empty outside method bodies. *)
  mutable method_self_ns : Refset'.t;
  (* When generating a custom constructor arg, holds the expected ML type
     for the argument (from the enclosing constructor's type params). Used
     by gen_ctor_call to recover concrete element types for nil lists when
     the ML type annotation has unresolved metas. *)
  mutable expected_ml_type_for_arg : ml_type option;
  (* Tracks which lifted function refs have already been emitted so that
     the same helper (e.g. _index_eq_dec_F) appears only once per file.
     Reset per-file via clear_seen_lifted_refs. *)
  mutable seen_lifted_refs : GlobRef.t list;
  mutable last_pair_accessor_any_cast : bool;
  (** When true, constructor expressions wrap each non-recursive field in
      [std::any] and force template args to [Tany].  Active while generating
      arguments for a call whose parameter type is erased to [std::any],
      so the constructed value's runtime type matches what the erased
      function body expects from [any_cast]. *)
  mutable wrap_for_any_param : bool;
  (** De Bruijn indices of pattern variables whose C++ struct field is
      stored as [std::any] due to type erasure.  Populated by
      {!populate_erased_field_env} during pattern-match branch setup;
      consulted by the [MLrel] and [MLmagic] handlers to emit
      [std::any_cast] when such a variable is used at a concrete type.
      Indices are shifted by {!push_env_types} and cleared by
      {!reset_env_types}. *)
  mutable cpp_erased_env : Escape.IntSet.t;
  (** Maps de Bruijn indices of [Tvar]-typed pattern variables to the
      concrete C++ type from the scrutinee's template arguments.
      For example, when matching [SigT<Tag, std::function<any(any)>>],
      the function field maps to [Tfun(\[Tany\], Tany)].  Used by
      [eta_fun] to detect that the callee's parameters are [std::any].
      Shifted and cleared together with {!cpp_erased_env}. *)
  mutable cpp_erased_type_env : cpp_type IntMap.t;
}

(** Mode for ITree effect extraction: sequential erases the tree,
    reified preserves it as [shared_ptr<ITree<R>>]. *)
and itree_extraction_mode =
  | Sequential  (* Default: erase itree E R to R, bind becomes ; *)
  | Reified     (* Preserve structure: itree E R becomes shared_ptr<ITree<R>> *)

(** The global mutable translation context, reset between top-level declarations. *)
let tctx =
  {
    current_type_vars = [];
    current_param_types = [];
    current_outer_function_name = None;
    current_cpp_return_type = None;
    env_types = [];
    pending_lifted_decls = [];
    current_letin_depth = 0;
    move_owned_vars = Escape.IntSet.empty;
    move_dead_after = Escape.IntSet.empty;
    move_suppress_tail = false;
    move_n_params = 0;
    match_param_counter = 0;
    promoted_var_map = [];
    in_constructor_expr = false;
    itree_mode = Sequential;
    eta_keep_moves = false;
    cs_counter = 0;
    method_self_ns = Refset'.empty;
    expected_ml_type_for_arg = None;
    seen_lifted_refs = [];
    last_pair_accessor_any_cast = false;
    wrap_for_any_param = false;
    cpp_erased_env = Escape.IntSet.empty;
    cpp_erased_type_env = IntMap.empty;
  }

let set_current_type_vars (tvars : Id.t list) = tctx.current_type_vars <- tvars
let get_current_type_vars () = tctx.current_type_vars
let clear_current_type_vars () = tctx.current_type_vars <- []

let set_current_param_types (params : (Id.t * ml_type) list) =
  tctx.current_param_types <- List.mapi (fun i (_, ty) -> (i + 1, ty)) params

let get_param_type_by_index (idx : int) : ml_type option =
  List.assoc_opt idx tctx.current_param_types

let clear_current_param_types () = tctx.current_param_types <- []

let lifted_decl_ref = function
  | Dtemplate (_, _, Dfundef ((r, _) :: _, _, _, _, _)) -> Some r
  | Dfundef ((r, _) :: _, _, _, _, _) -> Some r
  | _ -> None

(** Enqueue a declaration to be lifted to the enclosing scope.
    Skips duplicate declarations (same GlobRef) so that identical helpers
    (e.g. [_index_eq_dec_F]) are only emitted once per file even when
    multiple functions in the same module use them. *)
let add_lifted_decl (d : cpp_decl) =
  let is_dup =
    match lifted_decl_ref d with
    | None -> false
    | Some r ->
      List.exists (globref_equal r) tctx.seen_lifted_refs
  in
  if not is_dup then begin
    ( match lifted_decl_ref d with
    | Some r -> tctx.seen_lifted_refs <- r :: tctx.seen_lifted_refs
    | None -> () );
    tctx.pending_lifted_decls <- d :: tctx.pending_lifted_decls
  end

(** Drain and return the pending lifted declarations in definition order. *)
let take_lifted_decls () =
  let ds = List.rev tctx.pending_lifted_decls in
  tctx.pending_lifted_decls <- [];
  ds

(** Reset the seen-lifted-refs deduplication set. Call at the start of each
    new output file so identical helpers in different files are not suppressed. *)
let clear_seen_lifted_refs () = tctx.seen_lifted_refs <- []

(** Prepend bindings to the de Bruijn environment type stack.
    Also shifts all indices in {!cpp_erased_env} and {!cpp_erased_type_env}
    upward by [n] to account for the new bindings, keeping de Bruijn
    references consistent. *)
let push_env_types (ids : (Id.t * ml_type) list) =
  let n = List.length ids in
  if n > 0 && not (Escape.IntSet.is_empty tctx.cpp_erased_env) then begin
    tctx.cpp_erased_env <- Escape.IntSet.map (fun i -> i + n) tctx.cpp_erased_env;
    tctx.cpp_erased_type_env <- IntMap.fold (fun k v acc -> IntMap.add (k + n) v acc) tctx.cpp_erased_type_env IntMap.empty
  end;
  tctx.env_types <- ids @ tctx.env_types

(** Retrieve the ML type of the variable at de Bruijn index [i] (1-based). *)
let get_env_type (i : int) : ml_type = snd (List.nth tctx.env_types (pred i))

let get_env_type_opt (i : int) : ml_type option =
  if i <= 0 then None
  else match List.nth_opt tctx.env_types (pred i) with
       | Some (_, ty) -> Some ty
       | None -> None

(** Reset the environment type stack to empty.
    Also clears {!cpp_erased_env} and {!cpp_erased_type_env}. *)
let reset_env_types () =
  tctx.env_types <- [];
  tctx.cpp_erased_env <- Escape.IntSet.empty;
  tctx.cpp_erased_type_env <- IntMap.empty
