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
  CPPglob (r, tys, Some (Table.custom_info ?yields r))

(** Helper for local variables (VarRef) - no custom extraction applies *)
let mk_cppglob_local (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  CPPglob (r, tys, None)

(** Safe wrappers for Table lookups that may fail *)
let find_type_opt (r : GlobRef.t) : ml_type option =
  try Some (Table.find_type r) with Not_found -> None

(** What a binder of the lexical environment stands for ({!Lexenv.role}). *)
type binder_role = Lexenv.role =
  | Value
  | Dictionary

(** A declaration's parameter of type [ty] is its dictionary exactly when
    [ty] is a class: the one criterion the head generators promote a
    parameter to an instance by. *)
let parameter_role ty = if Table.is_typeclass_type ty then Dictionary else Value

(** A binder of the lexical environment ({!Lexenv.binder}). *)
type env_binder = Lexenv.binder = {
  eb_id : Id.t;
  eb_type : ml_type;
  eb_role : binder_role;
}

(** Consolidated mutable state for expression compilation.
    All fields except {!local_inductives} (which has a different lifecycle
    and is exported to [cpp.ml]) and the helpers being lifted
    ({!lifted_so_far}, which belong to a generation rather than a scope) live
    here. *)
type translation_ctx = {
  (* Template type variables for the function currently being translated. *)
  current_type_vars : Id.t list;
  (* The declaration's template head, verbatim: every parameter it declares,
     with the kind it declares it at.  Two questions are answered from it and
     neither can be answered from {!current_type_vars}, which keeps only the
     names and only the ML-indexed ones:

     - whether an occurrence may be written applied, which turns on [typename]
       versus [template <typename> class] (see {!is_current_typename_var});
     - which parameters are the enclosing class instances, which a lifted
       helper must redeclare because the body it lifts spells them (see
       {!current_class_temps}).

     Only the emitters that build the head know it, so a scope that does not
     say leaves this empty and both readers answer negatively. *)
  current_template_head : (template_type * Id.t) list;
  (* 1-indexed parameter types for the current function; used to recover
     erased type info at call sites. *)
  current_param_types : (int * ml_type) list;
  (* C++ return type of the enclosing function, set by gen_dfun. Used to
     recover erased template type args at call sites where C++ can't deduce
     them from lambda arguments. *)
  current_cpp_return_type : cpp_type option;
  (* De Bruijn environment: each variable's binder, with its ML type and
     role. *)
  env_types : Lexenv.t;
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
  (* The template parameter of the polymorphic function object being
     generated, if any.  Inside such a lambda every erased type denotes that
     one parameter -- it is the type the rank-2 binder quantified over -- so a
     producer with nothing else to say about a type argument says the carrier
     instead of [std::any].  See {!Rank2}. *)
  rank2_carrier : Id.t option;
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
  method_self_ns : Ref.User.Set.t;
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
    reified preserves it as [shared_ptr<ITree<R>>] ({!Core_effects.mode}). *)
and itree_extraction_mode = Core_effects.mode =
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
        current_template_head = [];
        current_param_types = [];
        current_cpp_return_type = None;
        env_types = Lexenv.empty;
        current_letin_depth = 0;
        move_owned_vars = Escape.IntSet.empty;
        move_dead_after = Escape.IntSet.empty;
        move_suppress_tail = false;
        move_n_params = 0;
        match_param_counter = 0;
        promoted_var_map = [];
        in_constructor_expr = false;
        rank2_carrier = None;
        itree_mode = Sequential;
        cs_counter = 0;
        pending_reuse_token = None;
        method_self_ns = Ref.User.Set.empty;
        cpp_binder_types = IntMap.empty;
    }

(** [with_field get set v f] runs [f] with one context field set to [v], and
    puts the enclosing value back on the way out however [f] leaves --
    returning or raising.

    Only the one field is restored, deliberately: the effects [f] means to
    have on the rest of the context (a counter advanced, a reuse token
    consumed) must survive, so saving and restoring the whole record would be
    wrong here even though it is right at a declaration boundary.

    Every dynamic-extent field gets a [with_*] built from this, so that no
    caller writes the save/set/restore by hand -- an omitted restore does not
    fail, it silently leaks the setting into whatever is translated next. *)
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

(** Accessors for {!translation_ctx.current_template_head}.  Set only by an
    emitter that has just built the declaration's template head, and restored
    by it on the way out; every other scope leaves the enclosing answer
    standing rather than guessing at one.  The readers below derive their
    answers from it rather than each keeping a list of their own. *)
let set_current_template_head (head : (template_type * Id.t) list) =
  tctx := { !tctx with current_template_head = head }
let get_current_template_head () = (!tctx).current_template_head

(** Whether the head declares [id] as a plain [typename], so that an applied
    occurrence of it cannot be written. *)
let is_current_typename_var (id : Id.t) =
  List.exists
    (fun (tt, i) ->
      Id.equal id i
      && match tt with TTtypename | TTtypename_default _ -> true | _ -> false )
    (!tctx).current_template_head

(** The head's concept-constrained parameters: the class instances the
    declaration is written against.  A helper lifted out of its body spells
    them, so it has to declare them too. *)
let current_class_temps () =
  List.filter
    (fun (tt, _) -> match tt with TTconcept _ -> true | _ -> false)
    (!tctx).current_template_head

(** Every type name the current declaration's head puts in scope: its
    ML-indexed type variables and the class instances it is written against.
    A resolved class field names the latter -- [typename StateV<_tcI0>::state]
    -- and is as much this scope's as [T1] is. *)
let current_scope_type_names () =
  (!tctx).current_type_vars @ List.map snd (current_class_temps ())

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
let with_method_self_ns (ns : Ref.User.Set.t) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.method_self_ns)
    (fun ns -> tctx := { !tctx with method_self_ns = ns })
    ns f

(** [with_promoted_var_map m f] runs [f] with [m] as the resolution for the
    promoted type variables in scope -- see {!translation_ctx.promoted_var_map}. *)
let with_promoted_var_map (m : (Id.t * cpp_type) list) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.promoted_var_map)
    (fun m -> tctx := { !tctx with promoted_var_map = m })
    m f

(** [with_in_constructor_expr b f] runs [f] with
    {!translation_ctx.in_constructor_expr} set to [b]. *)
let with_in_constructor_expr (b : bool) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.in_constructor_expr)
    (fun b -> tctx := { !tctx with in_constructor_expr = b })
    b f

(** [with_rank2_carrier x f] runs [f] with [x] as the carrier of the
    polymorphic function object being generated -- see {!Rank2}.  The extent
    is the lambda's body, so it has to be put back when that body is done. *)
let with_rank2_carrier (x : Id.t option) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.rank2_carrier)
    (fun x -> tctx := { !tctx with rank2_carrier = x })
    x f

(** The carrier of the polymorphic function object being generated, if any. *)
let get_rank2_carrier () = (!tctx).rank2_carrier

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

(** A match's branches are alternatives: each may consume the pending reuse
    token, since at most one of them runs.  [begin_alternatives] notes the
    token they start from, [enter_alternative] gives it to the next branch,
    [leave_alternative] notes whether that branch consumed it, and
    [end_alternatives] leaves it pending after the match only if none did --
    a later constructor on a path through a consuming branch would use it a
    second time. *)
type alternatives = {
  alt_start : (cpp_expr * GlobRef.t) option;
  mutable alt_consumed : bool;
}

let begin_alternatives () =
  {alt_start = (!tctx).pending_reuse_token; alt_consumed = false}

let enter_alternative a = tctx := { !tctx with pending_reuse_token = a.alt_start }

let leave_alternative a =
  if a.alt_start <> None && (!tctx).pending_reuse_token = None then
    a.alt_consumed <- true

let end_alternatives a =
  tctx :=
    { !tctx with
      pending_reuse_token = (if a.alt_consumed then None else a.alt_start) }

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

(** The helpers lifted so far out of the bodies the innermost
    {!collecting_lifted} is generating, newest first, and [None] outside every
    one.  Not a field of {!tctx}: a helper belongs to the generation it was
    lifted in, whatever scope inside that generation lifted it, so no scope
    restores it. *)
let lifted_so_far : cpp_decl list option ref = ref None

(** Lift a declaration out of the body being generated, to the generation
    collecting its helpers ({!collecting_lifted}).

    A helper's identity is the declaration it comes out of and the binder it
    was bound to there ({!Lifted}), so a generation lifting one identity
    twice lifts one helper and keeps the first.  That is sound only where
    both are the same declaration, which [CRANE_CHECK_IR] holds it to. *)
let add_lifted_decl (d : cpp_decl) =
  match !lifted_so_far with
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: a helper was lifted outside every generation that places one.")
  | Some ds -> (
    let same_helper d' =
      match (decl_globref d, decl_globref d') with
      | Some r, Some r' -> globref_equal r r'
      | _ -> false
    in
    match List.find_opt same_helper ds with
    | None -> lifted_so_far := Some (d :: ds)
    | Some d' ->
      if compare d d' <> 0 then
        Probe.violation "lifted helpers"
          Pp.(
            str "one generation lifted two different helpers as "
            ++ Option.cata GlobRef.print (mt ()) (decl_globref d)) )

(** [collecting_lifted f] runs [f] and returns, with its result, the helpers
    lifted out of the bodies it generated, in the order they were lifted: a
    generation's helpers are part of what it generates, for whoever records
    the generation to place. *)
let collecting_lifted f =
  let outer = !lifted_so_far in
  lifted_so_far := Some [];
  Fun.protect
    ~finally:(fun () -> lifted_so_far := outer)
    (fun () ->
      let v = f () in
      (v, List.rev (Option.default [] !lifted_so_far)) )

(** [relift ds] lifts [ds] again, to the generation collecting the current
    body's helpers: a generation that takes another's output takes the
    helpers lifted out of it along with it. *)
let relift ds = List.iter add_lifted_decl ds

(** Run [f] with the whole translation scope restored afterwards, however [f]
    leaves -- returning or raising.

    This is the bracket to reach for at a scope boundary: it saves the context
    wholesale, so it cannot forget a field the way an explicit list of fields
    can.  What [f] produces is not context: the helpers it lifts go to the
    generation collecting them ({!collecting_lifted}).  Use the single-field
    {!with_field} brackets instead where the point is precisely that the rest of
    the scope's effects must escape. *)
let with_scope f =
  let saved = !tctx in
  Fun.protect ~finally:(fun () -> tctx := saved) f

(** Prepend bindings to the de Bruijn environment type stack.
    Also shifts all indices in {!cpp_binder_types} upward by [n] to account
    for the new bindings, keeping de Bruijn references consistent. *)
let push_env_binders (binders : env_binder list) =
  let n = List.length binders in
  let shift m =
    if n > 0 && not (IntMap.is_empty m) then
      IntMap.fold (fun k v acc -> IntMap.add (k + n) v acc) m IntMap.empty
    else m
  in
  tctx := { !tctx with cpp_binder_types = shift (!tctx).cpp_binder_types };
  tctx := { !tctx with env_types = Lexenv.push binders (!tctx).env_types }

(** Prepend value bindings, innermost first. *)
let push_env_types (ids : (Id.t * ml_type) list) =
  push_env_binders (List.map (fun (eb_id, eb_type) -> { eb_id; eb_type; eb_role = Value }) ids)

(** Prepend a declaration's parameters, innermost first: each at a class type
    is a dictionary ({!parameter_role}). *)
let push_env_parameters (ids : (Id.t * ml_type) list) =
  push_env_binders
    (List.map (fun (eb_id, eb_type) -> { eb_id; eb_type; eb_role = parameter_role eb_type }) ids)

(** Restore the de Bruijn environment type stack to a [saved] prefix, undoing
    whatever {!push_env_types} did to {!cpp_binder_types} in between.

    A caller that saves and restores [env_types] by hand is closing a scope,
    and the binder types have to close with it: the entries for the binders
    being dropped go away, and everything the pushes shifted upward comes back
    down.  Leaving them shifted is worse than leaving them stale -- every
    surviving binder's recorded type then describes some other binder, so a
    concrete value can be read back as a box. *)
let restore_env_types (saved : Lexenv.t) =
  let n = Lexenv.depth (!tctx).env_types - Lexenv.depth saved in
  if n > 0 && not (IntMap.is_empty (!tctx).cpp_binder_types) then
    tctx :=
      { !tctx with
        cpp_binder_types =
          IntMap.fold
            (fun k v acc -> if k > n then IntMap.add (k - n) v acc else acc)
            (!tctx).cpp_binder_types IntMap.empty };
  tctx := { !tctx with env_types = saved }

(** Retrieve the ML type of the variable at de Bruijn index [i] (1-based). *)
let get_env_type (i : int) : ml_type =
  (List.nth ((!tctx).env_types :> env_binder list) (pred i)).eb_type

(** The binder at de Bruijn index [i] (1-based), or [None] when [i] is out of
    range (or non-positive). *)
let get_env_binder_opt (i : int) : env_binder option = Lexenv.binder (!tctx).env_types i

(** Like {!get_env_type} but returns [None] instead of raising when [i] is out
    of range (or non-positive). *)
let get_env_type_opt (i : int) : ml_type option =
  Option.map (fun b -> b.eb_type) (get_env_binder_opt i)

(** The ML type of the innermost binder named [id], if any. *)
let env_type_of_id (id : Id.t) : ml_type option =
  Option.map (fun b -> b.eb_type) (List.find_opt (fun b -> Id.equal b.eb_id id) ((!tctx).env_types :> env_binder list))

(** The lexical environment the traversal is generating code in. *)
let current_lexenv () : Lexenv.t = (!tctx).env_types

(** Reset the environment type stack to empty.
    Also clears {!cpp_binder_types}. *)
let reset_env_types () =
  tctx := { !tctx with env_types = Lexenv.empty };
  tctx := { !tctx with cpp_binder_types = IntMap.empty }
