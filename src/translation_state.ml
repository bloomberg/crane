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
  output : translation_output;  (** What the pass has produced; see below. *)
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

(** What a translation pass has {e produced}, as opposed to the scope it was
    producing it in.  Everything here outlives a nested scope: a declaration
    lifted out of a lambda still has to be emitted, and a helper already
    emitted must not be emitted again.

    Its purpose is to be the one field {!with_scope} carries out of the scope
    it restores.  Which state survives a scope is then settled by which record
    it sits in -- a field added to either one does the right thing by default,
    where a bracket that lists the fields it saves is one field away from
    being wrong. *)
and translation_output = {
  (* Declarations to be lifted to the enclosing scope (hoisted fixpoints). *)
  pending_lifted_decls : cpp_decl list;
  (* Tracks which lifted function refs have already been emitted so that
     the same helper (e.g. _index_eq_dec_F) appears only once per file.
     Reset per-file via clear_seen_lifted_refs. *)
  seen_lifted_refs : GlobRef.t list;
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
        output = {pending_lifted_decls = []; seen_lifted_refs = []};
        current_type_vars = [];
        current_param_types = [];
        current_outer_function_name = None;
        current_cpp_return_type = None;
        env_types = [];
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
        cpp_binder_types = IntMap.empty;
    }

(** [with_field get set v f] runs [f] with one context field set to [v], and
    puts the enclosing value back on the way out however [f] leaves --
    returning or raising.

    Only the one field is restored, deliberately: the effects [f] means to
    have on the rest of the context (a lifted declaration enqueued, a counter
    advanced) must survive, so saving and restoring the whole record would be
    wrong here even though it is right at a declaration boundary.

    Every dynamic-extent field gets a [with_*] built from this, so that no
    caller writes the save/set/restore by hand -- an omitted restore does not
    fail, it silently leaks the setting into whatever is translated next. *)
(** Modify the produced-so-far half of the context.  Every writer goes through
    this rather than rebuilding [tctx] in place, so {!with_scope} has exactly one
    field to carry across a scope boundary. *)
let update_output f = tctx := { !tctx with output = f (!tctx).output }

let with_field get set v f =
  let saved = get !tctx in
  set v;
  Fun.protect ~finally:(fun () -> set saved) f

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
  with_field (fun c -> c.current_type_vars) set_current_type_vars tvars f

(** [with_cpp_return_type ty f] runs [f] with [ty] as the enclosing function's
    C++ return type -- the type a tail expression is cast to. *)
let with_cpp_return_type (ty : cpp_type option) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.current_cpp_return_type)
    (fun t -> tctx := { !tctx with current_cpp_return_type = t })
    ty f

(** [with_param_types params f] runs [f] with [params] as the current
    function's parameters, indexed from 1. *)
let with_param_types (params : (Id.t * ml_type) list) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.current_param_types)
    (fun t -> tctx := { !tctx with current_param_types = t })
    (List.mapi (fun i (_, ty) -> (i + 1, ty)) params)
    f

(** [with_method_self_ns ns f] runs [f] with [ns] as the inductives whose
    methods are being generated, so self-references inside container types get
    the same [shared_ptr] wrapping as in the struct definition. *)
let with_method_self_ns (ns : Refset'.t) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.method_self_ns)
    (fun ns -> tctx := { !tctx with method_self_ns = ns })
    ns f

(** [with_in_constructor_expr b f] runs [f] with
    {!translation_ctx.in_constructor_expr} set to [b]. *)
let with_in_constructor_expr (b : bool) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.in_constructor_expr)
    (fun b -> tctx := { !tctx with in_constructor_expr = b })
    b f

(** [with_itree_mode m f] runs [f] extracting itree-typed terms in mode [m].
    The mode is a property of the declaration being generated, so it has to be
    put back when that declaration is done. *)
let with_itree_mode (m : itree_extraction_mode) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.itree_mode)
    (fun m -> tctx := { !tctx with itree_mode = m })
    m f

(** [with_move_suppress_tail b f] runs [f] with
    {!translation_ctx.move_suppress_tail} set to [b]. *)
let with_move_suppress_tail (b : bool) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.move_suppress_tail)
    (fun b -> tctx := { !tctx with move_suppress_tail = b })
    b f

(** [with_reuse_token tok f] runs [f] with [tok] as the pending Perceus reuse
    token.  The token is linear, and [f] clears it if it consumes it; the
    restore puts back whatever the enclosing scope had, consumed or not. *)
let with_reuse_token (tok : (cpp_expr * GlobRef.t) option) (f : unit -> 'a) : 'a
    =
  with_field
    (fun c -> c.pending_reuse_token)
    (fun t -> tctx := { !tctx with pending_reuse_token = t })
    tok f

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
  | Dtemplate (_, _, Dfun ((r, _) :: _, _, _, _)) -> Some r
  | Dfun ((r, _) :: _, _, _, _) -> Some r
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
      List.exists (globref_equal r) (!tctx).output.seen_lifted_refs
  in
  if not is_dup then begin
    ( match lifted_decl_ref d with
    | Some r ->
      update_output (fun o -> { o with seen_lifted_refs = r :: o.seen_lifted_refs })
    | None -> () );
    update_output (fun o ->
        { o with pending_lifted_decls = d :: o.pending_lifted_decls })
  end

(** Drain and return the pending lifted declarations in definition order. *)
let take_lifted_decls () =
  let ds = List.rev (!tctx).output.pending_lifted_decls in
  update_output (fun o -> { o with pending_lifted_decls = [] });
  ds

(** Reset the seen-lifted-refs deduplication set. Call at the start of each
    new output file so identical helpers in different files are not suppressed. *)
let clear_seen_lifted_refs () =
  update_output (fun o -> { o with seen_lifted_refs = [] })

(** Run [f] with the whole translation scope restored afterwards, however [f]
    leaves -- returning or raising -- while keeping everything [f] {e produced}.

    This is the bracket to reach for at a scope boundary: it saves the context
    wholesale and carries only {!translation_output} back out, so it cannot
    forget a field the way an explicit list of fields can.  Use the single-field
    {!with_field} brackets instead where the point is precisely that the rest of
    the scope's effects must escape. *)
let with_scope f =
  let saved = !tctx in
  Fun.protect ~finally:(fun () -> tctx := { saved with output = (!tctx).output }) f

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
