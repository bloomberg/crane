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

(** Helper to create CPPglob with pre-computed custom_info.  [yields] is what
    the global evaluates to, and is worth passing whenever the caller has the
    global's instantiated type: for a [%result] block template in value
    position it is the only record of the type, since there is no call node to
    carry one. *)
let mk_cppglob ?yields (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  let ci =
    {
      ci_inline = (if Table.to_inline r then Table.find_custom_opt r else None);
      ci_is_custom = Table.is_custom r;
      ci_yields = yields;
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
  current_type_vars : Id.t list;
  (* 1-indexed parameter types for the current function; used to recover
     erased type info at call sites. *)
  current_param_types : (int * ml_type) list;
  (* Name of the enclosing function, for diagnostic messages. *)
  current_outer_function_name : string option;
  (* C++ return type of the enclosing function, set by gen_dfun. Used to
     recover erased template type args at call sites where C++ can't deduce
     them from lambda arguments. *)
  current_cpp_return_type : cpp_type option;
  (* De Bruijn environment mapping variable indices to ML types. *)
  env_types : (Id.t * ml_type) list;
  (* Declarations to be lifted to the enclosing scope (hoisted fixpoints). *)
  pending_lifted_decls : cpp_decl list;
  (* Nesting depth of let ... in expressions; used for unique name
     generation in nested scopes. *)
  current_letin_depth : int;
  (* Escape analysis results: variables whose values are consumed (moved)
     exactly once, so they can be std::move'd. *)
  move_owned_vars : Escape.IntSet.t;
  (* Variables that are dead after this point (last use was in a move). *)
  move_dead_after : Escape.IntSet.t;
  (* True while generating a let-bound right-hand side: nothing nested in it
     is in the enclosing function's tail position, so tail-position moves must
     not fire.  Monotone within a function body -- inherited even by nested
     scopes that start a fresh {!Translation.slot} -- which is why it is
     context state rather than a slot property. *)
  move_suppress_tail : bool;
  (* Number of function parameters (offset for de Bruijn indices). *)
  move_n_params : int;
  (* Counter for generating unique match scrutinee variable names
     (_mp0, _mp1, ...). Reset at function boundaries. *)
  match_param_counter : int;
  (* Maps promoted record fields to their C++ qualified types.
     Example: "m_carrier" -> Tqualified(Tvar "_tcI0", "m_carrier")
     (prints as: typename _tcI0::m_carrier).
     Set by gen_dfun when generating template functions with typeclass
     parameters. Used by convert_ml_type_to_cpp_type to resolve
     [Tpromoted] markers. *)
  promoted_var_map : (Id.t * cpp_type) list;
  (* When true, we are inside a constructor expression (module-level static
     initializer). Promoted type vars that can't be resolved via
     promoted_var_map fall back to Tany (std::any) instead of keeping
     [Tpromoted] markers, because module-level aliases apply. *)
  in_constructor_expr : bool;
  (* ITree extraction mode: controls whether itree types are erased
     (Sequential) or preserved as shared_ptr<ITree<R>> (Reified). *)
  itree_mode : itree_extraction_mode;
  (* Counter for generating unique _cs / _cs1 / _cs2 cache variable names
     for Scustom_case scrutinee caching. Reset at function boundaries. *)
  cs_counter : int;
  (* Perceus reuse: when [Some (tok, ctor)] a reuse token [tok] (a moved,
     uniquely-owned matched recursive child) is available for the next
     [MLcons] of constructor [ctor]; that MLcons emits [<ctor>__reuse(tok, ...)]
     instead of the normal factory, then clears this. Set only inside a
     use_count()==1-guarded reuse arm in gen_cpp_case.

     The token is a linear resource -- exactly one MLcons may consume it, or
     two constructions would rebuild into the same storage -- so this is
     genuinely stateful and cannot become a {!Translation.slot} property: a
     threaded value would be visible to every sibling constructor at once. *)
  pending_reuse_token : (cpp_expr * Names.GlobRef.t) option;
  (* When generating a method body, holds the set of self-references
     (the inductive type(s) this method belongs to). Merged into the ns
     argument of convert_ml_type_to_cpp_type so that self-refs inside
     container types (e.g. List<tree>) get shared_ptr wrapping, matching
     the struct definition. Empty outside method bodies. *)
  method_self_ns : Refset'.t;
  (* Tracks which lifted function refs have already been emitted so that
     the same helper (e.g. _index_eq_dec_F) appears only once per file.
     Reset per-file via clear_seen_lifted_refs. *)
  seen_lifted_refs : GlobRef.t list;
  (** The C++ type of {e every} binder in scope, by de Bruijn index, paired
      with what decided it.

      A binder is typed once, where it is bound ({!Bbinding}, written by
      [push_binders]); a pattern match that pins a field down more precisely
      than its definition-site type says -- matching [SigT<Tag,
      std::function<any(any)>>] records [Tfun (\[Tany\], Tany)] for the
      function field -- overrides it ({!Bpattern}, written by
      [populate_erased_field_env]).  Whether a binder is boxed is read off
      this map rather than tracked beside it, so the two answers cannot drift
      apart.

      Shifted by {!push_env_types} and cleared by {!reset_env_types}. *)
  cpp_binder_types : (cpp_type * binder_origin) IntMap.t;
}

(** What decided a binder's C++ type, and so which answer wins when both are
    available: an instantiation a pattern match pinned down is more precise
    than the type the binder was given where it was bound. *)
and binder_origin =
  | Bbinding  (** Assigned at the binding site, from the binder's ML type *)
  | Bpattern  (** Pinned down by the scrutinee's instantiation in a branch *)

(** Mode for ITree effect extraction: sequential erases the tree,
    reified preserves it as [shared_ptr<ITree<R>>]. *)
and itree_extraction_mode =
  | Sequential  (* Default: erase itree E R to R, bind becomes ; *)
  | Reified     (* Preserve structure: itree E R becomes shared_ptr<ITree<R>> *)

(** The global translation context, reset between top-level declarations.

    The record is immutable and the mutability lives in this one [ref], so
    saving and restoring the context around a subtree is total: [let saved =
    !tctx in ... ; tctx := saved] cannot forget a field, whatever fields are
    added later. *)
let tctx =
  ref
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
        cs_counter = 0;
        pending_reuse_token = None;
        method_self_ns = Refset'.empty;
        seen_lifted_refs = [];
        cpp_binder_types = IntMap.empty;
    }

(** Accessors for {!translation_ctx.current_type_vars}: the template type
    variables in scope for the function currently being translated.

    Reach for {!with_type_vars} first.  These two are for the few scopes whose
    extent is not a lexical one -- opened partway through a declaration
    emitter and closed at each of its exits. *)
let set_current_type_vars (tvars : Id.t list) =
  tctx := { !tctx with current_type_vars = tvars }
let get_current_type_vars () = (!tctx).current_type_vars
let clear_current_type_vars () = tctx := { !tctx with current_type_vars = [] }

(** [with_type_vars tvars f] runs [f] with [tvars] as the type-variable scope,
    and puts the enclosing scope back on the way out however [f] leaves --
    returning or raising.

    Prefer this to a hand-written save/set/restore wherever the scope's extent
    is a lexical one.  Everything that converts a type reads the scope
    ambiently (see {!Translation.cpp_of_ml}), so a restore that a path skips
    does not fail: the next conversion quietly numbers its type variables
    against the wrong function. *)
let with_type_vars (tvars : Id.t list) (f : unit -> 'a) : 'a =
  let saved = get_current_type_vars () in
  set_current_type_vars tvars;
  Fun.protect ~finally:(fun () -> set_current_type_vars saved) f

(** Accessors for {!translation_ctx.current_param_types}: the 1-indexed
    parameter types of the current function, used to recover erased type info
    at call sites. [set_current_param_types] assigns the 1-based indices. *)
let set_current_param_types (params : (Id.t * ml_type) list) =
  tctx :=
    { !tctx with
      current_param_types = List.mapi (fun i (_, ty) -> (i + 1, ty)) params }

let get_param_type_by_index (idx : int) : ml_type option =
  List.assoc_opt idx (!tctx).current_param_types

let clear_current_param_types () =
  tctx := { !tctx with current_param_types = [] }

(** The defining [GlobRef.t] of a lifted declaration, if it has one.
    Used by {!add_lifted_decl} to deduplicate identical hoisted helpers. *)
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
      List.exists (globref_equal r) (!tctx).seen_lifted_refs
  in
  if not is_dup then begin
    ( match lifted_decl_ref d with
    | Some r ->
      tctx := { !tctx with seen_lifted_refs = r :: (!tctx).seen_lifted_refs }
    | None -> () );
    tctx :=
      { !tctx with pending_lifted_decls = d :: (!tctx).pending_lifted_decls }
  end

(** Drain and return the pending lifted declarations in definition order. *)
let take_lifted_decls () =
  let ds = List.rev (!tctx).pending_lifted_decls in
  tctx := { !tctx with pending_lifted_decls = [] };
  ds

(** Reset the seen-lifted-refs deduplication set. Call at the start of each
    new output file so identical helpers in different files are not suppressed. *)
let clear_seen_lifted_refs () = tctx := { !tctx with seen_lifted_refs = [] }

(** Prepend bindings to the de Bruijn environment type stack.
    Also shifts all indices in {!cpp_binder_types} upward by [n] to account
    for the new bindings, keeping de Bruijn references consistent. *)
let push_env_types (ids : (Id.t * ml_type) list) =
  let n = List.length ids in
  let shift m =
    if n > 0 && not (IntMap.is_empty m) then
      IntMap.fold (fun k v acc -> IntMap.add (k + n) v acc) m IntMap.empty
    else m
  in
  tctx := { !tctx with cpp_binder_types = shift (!tctx).cpp_binder_types };
  tctx := { !tctx with env_types = ids @ (!tctx).env_types }

(** Retrieve the ML type of the variable at de Bruijn index [i] (1-based). *)
let get_env_type (i : int) : ml_type = snd (List.nth (!tctx).env_types (pred i))

(** Like {!get_env_type} but returns [None] instead of raising when [i] is out
    of range (or non-positive). *)
let get_env_type_opt (i : int) : ml_type option =
  if i <= 0 then None
  else match List.nth_opt (!tctx).env_types (pred i) with
       | Some (_, ty) -> Some ty
       | None -> None

(** Reset the environment type stack to empty.
    Also clears {!cpp_binder_types}. *)
let reset_env_types () =
  tctx := { !tctx with env_types = [] };
  tctx := { !tctx with cpp_binder_types = IntMap.empty }
