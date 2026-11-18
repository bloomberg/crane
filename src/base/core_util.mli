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

(** Utility functions over Core types and terms, type environments, and
    optimization passes.  Shared by every stage that handles Core: type
    reconstruction in extraction, the {!normalize} simplifier that
    {!Core_passes.Modutil.optimize_struct} runs, and the backend's readers of types and
    global uses. *)

open Names

(** {2 Generic traversals}

    Each sees through a resolved meta and visits every child type, a [Core.Type.Variable_app]'s
    arguments included. *)

(** Sets of type variable indices. *)
module IntSet : Stdlib.Set.S with type elt = int and type t = Stdlib.Set.Make(Stdlib.Int).t

(** [t] with every resolved meta at its root taken off. *)
val core_resolve : 'p Core.Type.at -> 'p Core.Type.at

(** The immediate sub-types of an already resolved type. *)
val core_type_children : 'p Core.Type.at -> 'p Core.Type.at list

(** Whether some node of the type, the root included, satisfies [p]. *)
val exists_core_type : ('p Core.Type.at -> bool) -> 'p Core.Type.at -> bool

(** Pre-order: [f] sees a node before its children. *)
val fold_core_type : ('a -> 'p Core.Type.at -> 'a) -> 'a -> 'p Core.Type.at -> 'a

(** Bottom-up: [f] sees a node after its children were mapped. *)
val map_core_type : ('p Core.Type.at -> 'p Core.Type.at) -> 'p Core.Type.at -> 'p Core.Type.at

(** The indices of every type variable in [t], an applied one included. *)
val core_tvars : 'p Core.Type.at -> IntSet.t

(** {2 Utility functions over Core types with meta} *)

(** Reset the meta variable counter. *)
val reset_meta_count : unit -> unit

(** [preserving_meta_supply f] is [f ()], with the metavariable counter and
    the pending applications put back as they were: open annotations are
    compared by number, so a check that reruns a pass must not move the
    numbers the run it checks goes on to make. *)
val preserving_meta_supply : (unit -> 'a) -> 'a

(** Create a fresh meta variable; once the program is frozen, an open
    annotation instead. *)
val new_meta : 'a -> Core.Type.extracted

(** A fresh open annotation, at any phase: what {!new_meta} makes once the
    program is frozen. *)
val new_open : unit -> 'p Core.Type.at

(** {!new_meta} at the phase of the cell given, which is extracted: for a
    reader of a type of any phase that copies a metavariable it meets. *)
val new_meta_like : 'p Core.Extracted.Meta.cell -> 'p Core.Type.at

(** Apply a type to arguments, contracting the application when the head is
    known. A head that carries placeholders -- an eta-expanded constructor, or
    a type-level lambda whose binder extraction could not name -- has them
    filled rather than extended. *)
val apply_core_type : 'p Core.Type.at -> 'p Core.Type.at list -> 'p Core.Type.at

(** Substitute type variables using a list of types.
    @param l replacement types for [Core.Type.Variable 1], [Core.Type.Variable 2], ... in order
    @param t the Core type to substitute into *)
val type_subst_list : 'p Core.Type.at list -> 'p Core.Type.at -> 'p Core.Type.at

(** [type_subst_fun f t] substitutes each [Core.Type.Variable j] for which [f j] answers,
    leaving the others unchanged. *)
val type_subst_fun : (int -> 'p Core.Type.at option) -> 'p Core.Type.at -> 'p Core.Type.at

(** A one-line rendering of a Core type, for diagnostics. *)
val debug_core_type : 'p Core.Type.at -> string

(** The scheme extraction recorded for [r], with the source binders its
    variables come from; [None] for anything but an extracted constant. *)
val recorded_schema : GlobRef.t -> Core.Schema.t option

(** The scheme a reference to [r] is at: the one extraction recorded, or
    else one minted at the arity of the type [r] is registered with, the
    same one at every reference.  [None] for a declaration quantifying
    nothing, or with no type. *)
val reference_scheme : GlobRef.t -> Core.Scheme.Id.t option

(** A reference to the declaration [r] that a pass synthesises: open
    ({!Global_use.infer_all}) at [r]'s scheme -- the recorded one, or one
    of the arity [r]'s registered type has -- and monomorphic for a
    declaration quantifying nothing. *)
val open_reference : GlobRef.t -> 'p Core.Global_use.at

(** A declaration's reference to itself in its own body
    ({!Global_use.identity}). *)
val self_reference : GlobRef.t -> 'p Core.Global_use.at

(** A call to [target] written at the caller's own variables, in order: what
    a forwarder with [target]'s type writes. *)
val forwarding_use : GlobRef.t -> 'p Core.Global_use.at

(** Types for a callee's scheme variables, keyed by {!Core.Scheme.Var.t}: what a
    use wrote, a call's reading of them, or what its arguments imply.  Every
    variable up to the last one a reading speaks for has a type -- whatever
    the reading fills an open one with -- and past it there is none.  The
    types are reached only through the variable they are for, never by
    position, so they cannot be paired by position with a source binder, an
    argument or a template parameter. *)
module Var_types : sig
  (** The types, by variable. *)
  type 'p t

  (** No variable spoken for. *)
  val empty : 'p t

  (** Whether no variable is spoken for. *)
  val is_empty : 'p t -> bool

  (** [through last f]: every variable of [last]'s scheme up to [last],
      variable [v] at [f v]; {!empty} for [None]. *)
  val through : Core.Scheme.Var.t option -> (Core.Scheme.Var.t -> 'p Core.Type.at) -> 'p t

  (** Variable [v]'s type, if it is spoken for; [Invalid_argument] for a
      variable of another scheme, which is a caller confusing two schemes. *)
  val find : 'p t -> Core.Scheme.Var.t -> 'p Core.Type.at option

  (** {!find} at the variable the callee's own type spells [Core.Type.Variable (_, i)]
      ({!Core.Scheme.Var.of_tvar}): for a reader holding a variable it met in
      that type. *)
  val find_tvar : 'p t -> int -> 'p Core.Type.at option

  (** Each variable spoken for, in ascending order, with its type. *)
  val bindings : 'p t -> (Core.Scheme.Var.t * 'p Core.Type.at) list

  (** [apply t ty] instantiates [ty], a type in the callee's scheme
      variables: each variable spoken for is replaced, any other stays. *)
  val apply : 'p t -> 'p Core.Type.at -> 'p Core.Type.at

  (** The same variables at equal types ({!eq_core_type}). *)
  val equal : 'p t -> 'p t -> bool
end

(** The greatest of [vars], all of one scheme; [None] for none. *)
val last_var : Core.Scheme.Var.t list -> Core.Scheme.Var.t option

(** The arguments [use] wrote, for the scheme variables they are for, up to
    the last variable written. *)
val written_type_args : 'p Core.Global_use.at -> 'p Var_types.t

(** [subst_written_evidence use t] is [t], a type in [use]'s callee's
    scheme variables, with each variable the use wrote an argument for at
    that variable's own binder replaced by the argument.  A variable the use
    did not write is left unchanged, and an argument written at a binder with
    no variable replaces nothing. *)
val subst_written_evidence : 'p Core.Global_use.at -> 'p Core.Type.at -> 'p Core.Type.at

(** [instantiate_body ~reader use body] is a copy of [body], the callee's
    definition, at [use]: its types read at the arguments the use wrote
    ({!instantiate_written}), the uses inside it composed with that reading,
    and every hole they leave open renamed apart from the original's -- a
    copy is new uses, which do not share what they leave open. *)
val instantiate_body : reader:string -> 'p Core.Global_use.at -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Whether [use] wrote an argument for each of its callee's variables
    [1 .. n] at that variable's own binder. *)
val written_covers : 'p Core.Global_use.at -> int -> bool

(** {2 Frozen instantiations} *)

(** [freeze_types tys] copies [tys] with every solved metavariable replaced
    by its contents and every unsolved one by a {!Core.Type.Hole} -- one per
    metavariable, shared by the copies, and distinct from every hole minted
    before. *)
val freeze_types : 'p Core.Type.at list -> 'p Core.Type.at list

(** A hole distinct from every other. *)
val fresh_hole : unit -> 'p Core.Type.at

(** Whether the type mentions a metavariable, solved or not. *)
val type_has_meta : 'p Core.Type.at -> bool

(** A callee's type at a use's frozen instantiation: every variable the
    instantiation solves is replaced, so the result may hold holes.  It is
    not an ordinary Core type until {!close} says it is hole-free or
    {!resolve} has filled its holes from other evidence. *)
module Partial : sig
  (** A type that may hold holes. *)
  type 'p t = private 'p Core.Type.at

  (** [instantiate inst ty] is [ty], in the callee's scheme variables, with
      each variable [inst] solves to a type replaced by that type, which may
      hold holes; a variable it leaves standing for itself
      ({!Core.Scheme.Identity}) stays. *)
  val instantiate : 'p Core.Type.at Core.Scheme.Instantiation.t -> 'p Core.Type.at -> 'p t

  (** The holes, in order of first occurrence. *)
  val holes : 'p t -> int list

  (** The type, when it holds no hole. *)
  val close : 'p t -> 'p Core.Type.at option

  (** Fills each hole [h] for which [f h] answers. *)
  val resolve : (int -> 'p Core.Type.at option) -> 'p t -> 'p t
end

(** {!subst_written_evidence}, the reading a substitution reader makes.
    Under [CRANE_PROBE] it is compared with the reading at the use's solved
    instantiation ([INSTW_same], [INSTW_differ], [INSTW_holes]). *)
val instantiate_written : reader:string -> 'p Core.Global_use.at -> 'p Core.Type.at -> 'p Core.Type.at

(** Substitute type variables using an array of types.
    @param v replacement types for [Core.Type.Variable 1], [Core.Type.Variable 2], ... (zero-indexed in the array)
    @param t the Core type to substitute into *)
val type_subst_vect : 'p Core.Type.at array -> 'p Core.Type.at -> 'p Core.Type.at

(** [instantiate_prenex n t] instantiates the prenex type [t], quantifying
    [Core.Type.Variable 1 .. Core.Type.Variable n], with fresh meta variables. *)
val instantiate_prenex : int -> Core.Type.extracted -> Core.Type.extracted

(** Replace every [Core.Type.Unknown] with a fresh metavariable, so that an erased
    existential can unify with a concrete type at a use site. *)
val instantiate_unknowns : Core.Type.extracted -> Core.Type.extracted

(** Attempt most general unification of two types.  Mutably updates
    metavariable bindings on success; silently does nothing on failure.
    @param t1 first type
    @param t2 second type *)
val try_mgu : 'p Core.Type.at -> 'p Core.Type.at -> unit

(** Determine if a type coercion requires magic (unsafe cast).
    @param p a pair [(expected, actual)] of Core types to compare
    @return [true] if the types cannot be unified and [Core.Expr.Coerce] is needed *)
val needs_magic : 'p Core.Type.at * 'p Core.Type.at -> bool

(** Conditionally wrap a Core term in a coercion.  The two types are passed
    explicitly because {!needs_magic}'s pair is unordered ([mgu] is
    symmetric) whereas a backend must know which side the term is on.
    @param from the type the term itself has
    @param into the type the context requires
    @param b    when [true], wraps [a]
    @param a    the Core expression to (possibly) wrap *)
val put_magic_if :
  from:'p Core.Type.at -> into:'p Core.Type.at -> bool -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Wrap a Core term in a coercion iff its own type fails to unify with the one
    its context requires.
    @param from the type the term itself has
    @param into the type the context requires
    @param a    the Core expression to (possibly) wrap *)
val put_magic : from:'p Core.Type.at -> into:'p Core.Type.at -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Check if a Core term can be generalized at a let.  For C++ an
    application never is; anything else is, an approximation that well-typed
    Rocq never exercises. *)
val generalizable : 'p Core.Expr.at -> bool

(** {2 Core type environment} *)

module Type_env : sig
  (** Type schemas of the binders in scope, innermost first, with the free
      metavariables they mention. *)
  type t

  (** The empty type environment. *)
  val empty : t

  (** Get the n-th most recently entered schema and instantiate it.
      @param type_env the type environment
      @param n 1-based index into the environment (1 = most recently pushed)
      @return a fresh instantiation of the n-th schema *)
  val get : t -> int -> Core.Type.extracted

  (** Add a type to the environment, after generalizing free meta variables.
      @param type_env the current environment
      @param t  the Core type to generalize and push *)
  val push_gen : t -> Core.Type.extracted -> t

  (** Add a type with no [Core.Type.Variable] (no generalization needed).
      @param type_env the current environment
      @param t  the monomorphic Core type to push *)
  val push_type : t -> Core.Type.extracted -> t

  (** Add a type with no [Core.Type.Variable] nor [Core.Type.Meta] (no generalization, no free metas).
      @param type_env the current environment
      @param t  the ground Core type to push *)
  val push_std_type : t -> Core.Type.extracted -> t
end

(** {2 Utility functions over Core types without meta} *)

(** Check if a mutual inductive name occurs in a type.
    @param kn the mutual inductive kernel name to search for
    @param t  the Core type to search in
    @return [true] if [kn] appears inside a [Core.Type.Global_app] node of [t] *)
val type_mem_kn : MutInd.t -> 'p Core.Type.at -> bool

(** Return the maximum type variable index in a type.
    @return the largest [i] such that [Core.Type.Variable (Schematic, i)] occurs in [t], or
            [0] if none does.  [Core.Type.Rigidity.Rigid] nodes are not considered. *)
val type_maxvar : 'p Core.Type.at -> int

(** Whether a type carries a [Core.Type.Unknown] hole -- the spelling extraction gives a
    type-level lambda, whose binder is where the hole is.  See
    {!fill_placeholders}. *)
val type_has_hole : 'p Core.Type.at -> bool

(** Whether the arguments of an application carry a hole past their trailing
    run of placeholders.  That run is eta-expansion, which the next argument
    replaces; a hole anywhere else is the binder of a type-level lambda --
    [fun Z => EOU (MaybePoison Z)] arrives as [EOU (MaybePoison _)] -- and
    applying it fills every occurrence.  [~generated:false], for a mapped
    head, counts only a hole standing as an argument itself: a nested one is
    the argument's own placeholder (see {!fill_placeholders}), and so is a
    hole inside an argument at one of the [~constructors] positions, a type
    alias's parameter its definition applies ({!constructor_params}). *)
val writes_binder : ?generated:bool -> ?constructors:int list -> 'p Core.Type.at list -> bool

(** The 0-based positions of the parameters the type alias [r] applies in its
    definition, as far as that definition has been extracted; none for
    anything else. *)
val constructor_params : GlobRef.t -> int list

(** [fill_type_hole a t] is [t] with its [Core.Type.Unknown] holes filled by [a]: the
    type-level lambda {!type_has_hole} recognises, applied to [a]. *)
val fill_type_hole : 'p Core.Type.at -> 'p Core.Type.at -> 'p Core.Type.at

(** Decompose a Core type into a list of argument types and a result type.
    @return [(args, result)] where [args] are the curried parameter types
            and [result] is the final return type *)
val type_decomp : 'p Core.Type.at -> 'p Core.Type.at list * 'p Core.Type.at

(** Recompose a Core type from a list of argument types and a result type.
    @param args the list of argument types (left-to-right)
    @param result the final return type *)
val type_recomp : 'p Core.Type.at list * 'p Core.Type.at -> 'p Core.Type.at

(** Make every [Core.Type.Rigidity.Schematic] type variable [Core.Type.Rigidity.Rigid], so that it no longer
    unifies with the schematic variables of any other type scheme.  Applied to
    a constant's own type before its body is reconstructed. *)
val rigidify : 'p Core.Type.at -> 'p Core.Type.at

(** Abbreviation map type for looking up type aliases. *)
type 'p abbrev_map = GlobRef.t -> 'p Core.Type.at option

(** Expand type abbreviations using the given map.
    @param env lookup function mapping global references to their type bodies;
               return [None] to leave a [Core.Type.Global_app] unexpanded
    @param t   the Core type to expand *)
val type_expand : 'p abbrev_map -> 'p Core.Type.at -> 'p Core.Type.at

(** Simplify a Core type: {!type_expand} with no abbreviation, which only
    replaces solved metavariables by their contents (when type expansion is
    enabled). *)
val type_simpl : 'p Core.Type.at -> 'p Core.Type.at

(** Convert a Core type to a signature element for its outermost position.
    @param env abbreviation map for expanding type aliases
    @param t   the Core type to classify
    @return [Core.Signature.Argument.Erased d] if the outermost type is [Core.Type.Erased d] (and not conservative),
            [Core.Signature.Argument.Runtime] otherwise *)
val type_to_sign : 'p abbrev_map -> 'p Core.Type.at -> Core.Signature.Argument.t

(** Convert a Core type to a full argument signature by decomposing arrows.
    @param env abbreviation map for expanding type aliases
    @param t   the Core type to decompose
    @return a [Core.Signature.t] with one entry per curried argument position *)
val type_to_signature : 'p abbrev_map -> 'p Core.Type.at -> Core.Signature.t

(** Expunge dummy arguments from a Core type using the abbreviation map.
    @param env abbreviation map for expanding type aliases
    @param t   the Core type from which to remove [Core.Type.Erased] arrows *)
val type_expunge : 'p abbrev_map -> 'p Core.Type.at -> 'p Core.Type.at

(** Expunge dummy arguments from a Core type guided by a pre-computed signature.
    @param env abbreviation map for expanding type aliases
    @param s   the signature indicating which arguments are [Core.Signature.Argument.Erased]
    @param t   the Core type from which to remove the killed arrow positions *)
val type_expunge_from_sign : 'p abbrev_map -> Core.Signature.t -> 'p Core.Type.at -> 'p Core.Type.at

(** Test equality of two Core types. *)
val eq_core_type : 'p Core.Type.at -> 'q Core.Type.at -> bool

(** Check if a type is Core.Type.Erased. *)
val is_erased_type : 'p Core.Type.at -> bool

(** Check if a Core term is Core.Expr.Erased_value. *)
val is_erased_value : 'p Core.Expr.at -> bool

(** The term definitions a declaration makes: a [Core.Decl.Value]'s one, a [Core.Decl.Recursive_group]'s
    group, and none for anything else. *)
val term_defs : 'p Core.Decl.at -> 'p Core.Recursion.Definition.at list

(** Whether a signature entry is [Erased] (any reason). *)
val isKill : Core.Signature.Argument.t -> bool

(** Expunge dummy arguments from a case expression, eta-expanding as needed.
    @param types
      one type per signature element, used to type the binders introduced when
      eta-expanding; binders past the end of the list get [Core.Type.Unknown]
    @param s the signature indicating which leading arguments are [Core.Signature.Argument.Erased]
    @param e the Core expression (typically a match branch body) to process
    @return [(ids, body)] with the surviving binders and the stripped body *)
val case_expunge :
  ?types:'p Core.Type.at list ->
  Core.Signature.t ->
  'p Core.Expr.at ->
  (Core.Binder_name.t * 'p Core.Type.at) list * 'p Core.Expr.at

(** Expunge dummy leading lambdas from a term according to a signature.
    Leaves one dummy lambda when all arguments are logical and the target
    language is strict.
    @param s        the signature indicating which leading lambdas are [Core.Signature.Argument.Erased]ed
    @param ids_body a pair [(binders, body)] as returned by [collect_lams]
    @return the term with the erased lambdas removed *)
val term_expunge : Core.Signature.t -> (Core.Binder_name.t * 'p Core.Type.at) list * 'p Core.Expr.at -> 'p Core.Expr.at

(** {2 Special identifiers}

    [anonymous_name] is [x]; [dummy_name], [_x], marks dead code. *)

(** The anonymous identifier used for unnamed binders. *)
val anonymous_name : Id.t

(** The dummy identifier used for dead code. *)
val dummy_name : Id.t

(** Convert a Rocq [Name.t] to an [Id.t]: {!anonymous_name} for an anonymous
    name or {!dummy_name}. *)
val id_of_name : Name.t -> Id.t

(** Move a name out of the space Crane reserves for the locals it invents
    itself ([_stack], [_result], ...) by carrying its leading underscores to
    the end.  Unchanged when there are none, when the name is all underscores,
    or when a digit would be left in front ([_0] stays [_0]; [0_] is not an
    identifier). *)
val unreserve_leading_underscore : string -> string

(** The [n]th temporary of a declaration: the binder {!Core_plan.Normalize} gives a
    call it takes out of an expression.  The name is in the space Crane
    reserves for itself, which no Rocq binder reaches (see
    {!unreserve_leading_underscore}), so the name alone says what the binding
    is, at every stage down to the printer. *)
val temporary_id : int -> Id.t

(** Whether [id] is a {!temporary_id}. *)
val is_temporary_id : Id.t -> bool

(** Extract the Id.t from an Core.Binder_name.t.  A temporary keeps its reserved name. *)
val id_of_binder_name : Core.Binder_name.t -> Id.t

(** Generate a temporary identifier from an Core.Binder_name.t. *)
val tmp_id : Core.Binder_name.t -> Core.Binder_name.t

(** Whether a term does nothing but raise -- an unrealised axiom counts.  Binders in front of the raise do
    not change that: nothing gets to be bound, because the raise comes first.
    Such a definition is spelled as a zero-argument function, so that it
    throws when called rather than at static initialisation. *)
val only_throws : 'p Core.Expr.at -> bool

(** {2 Lambda collection}

    [collect_lams (Lambda (id1, ..., Lambda (idn, t) ...))] returns the list [idn;...;id1]
    and the term [t]. *)

(** Collect all lambda abstractions from a term. *)
val collect_lams : 'p Core.Expr.at -> (Core.Binder_name.t * 'p Core.Type.at) list * 'p Core.Expr.at

(** Collect exactly n lambda abstractions from a term.
    @param n the number of leading [Core.Expr.Lambda] nodes to collect; asserts if fewer exist
    @param t the term to peel
    @return [(binders, body)] where [binders] has exactly [n] entries
            (innermost first, as {!collect_lams} returns them) *)
val collect_n_lams : int -> 'p Core.Expr.at -> (Core.Binder_name.t * 'p Core.Type.at) list * 'p Core.Expr.at

(** Remove n lambda abstractions from a term.
    @param n the number of leading [Core.Expr.Lambda] nodes to drop; asserts if fewer exist *)
val remove_n_lams : int -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Count the number of lambda abstractions at the head of a term. *)
val nb_lams : 'p Core.Expr.at -> int

(** Wrap a term in lambda abstractions with the given identifiers and types:
    the converse of {!collect_lams}.
    @param ids list of [(identifier, type)] pairs, innermost binder first
    @param a   the body to wrap *)
val named_lams : (Core.Binder_name.t * 'p Core.Type.at) list -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Wrap a term in n dummy lambda abstractions.
    @param a the body to wrap
    @param n the number of [Core.Expr.Lambda(Dummy,...)] layers to add *)
val dummy_lams : 'p Core.Expr.at -> int -> 'p Core.Expr.at

(** Wrap a term in anonymous or dummy lambda abstractions based on the
    signature: a [Core.Signature.Argument.Runtime] entry becomes an anonymous lambda at its type among
    [types], a [Core.Signature.Argument.Erased k] entry a [Core.Binder_name.Anonymous] lambda at [Core.Type.Erased k].
    @param a     the body to wrap
    @param types one Core type per signature entry, matched positionally;
                 falls back to [Core.Type.Axiom] when the list runs out
    @param s     the signature driving the lambda structure *)
val anonym_or_dummy_lams_typed : 'p Core.Expr.at -> 'p Core.Type.at list -> Core.Signature.t -> 'p Core.Expr.at

(** Generate eta-expanded argument list based on arity and signature.
    @param n the starting de Bruijn level (counts down)
    @param s the signature; [Core.Signature.Argument.Runtime] entries emit [Core.Expr.Bound_variable] arguments,
             [Core.Signature.Argument.Erased] entries are skipped
    @return the list of [Core.Expr.Bound_variable] arguments for the kept positions *)
val eta_args_sign : int -> Core.Signature.t -> 'p Core.Expr.at list

(** {2 Utility functions over Core terms} *)

(** Apply a Core term to a list of arguments. Returns [f] unchanged when [a] is empty. *)
val apply_args : 'p Core.Expr.at -> 'p Core.Expr.at list -> 'p Core.Expr.at

(** Map a function over all immediate subterms.
    @param f the transformation to apply to each direct child
    @param t the Core node whose children are to be mapped *)
val ast_map : ('p Core.Expr.at -> 'p Core.Expr.at) -> 'p Core.Expr.at -> 'p Core.Expr.at

(** [ast_map_types f a] rewrites every [Core.Type.t] embedded in [a] with [f],
    recursing through the whole term. *)
val ast_map_types : ('p Core.Type.at -> 'p Core.Type.at) -> 'p Core.Expr.at -> 'p Core.Expr.at

(** [e] with each of its open metavariables replaced by a fresh one, the same
    one wherever [e] shares it: a pass that fills holes in the copy, as type
    recovery does, then leaves [e] itself as it was for the next pass. *)
val freshen_metas : 'p Core.Expr.at -> 'p Core.Expr.at

(** [a] with the holes of its global uses renamed apart from every other, the
    same new hole wherever [a] shares one: a copy is new uses, which leave
    open what their originals did independently of them. *)
val freshen_holes : 'p Core.Expr.at -> 'p Core.Expr.at

(** [has_unknown t]: whether [t] mentions [Core.Type.Unknown], the marker extraction
    leaves where a type was erased. *)
val has_unknown : 'p Core.Type.at -> bool

(** [recover_erased_types expected a] fills in the annotations extraction
    erased to [Core.Type.Unknown], using the type [a] is known to have. Only erased
    annotations are touched, and only where the context supplies something
    better. *)
val recover_erased_types :
  ?only:(Core.Type.t -> bool) ->
  ?refine_only:bool ->
  Core.Type.t ->
  Core.Expr.t ->
  Core.Expr.t

(** Map a function over all immediate subterms with a binding-depth counter.
    @param f   the transformation; receives the current depth and the child term
    @param n   the current binding depth (passed to [f] for each child)
    @param t   the Core node whose children are to be mapped *)
val ast_map_lift : (int -> 'p Core.Expr.at -> 'p Core.Expr.at) -> int -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Iterate a function over all immediate subterms.
    @param f the action to perform on each direct child
    @param t the Core node to iterate over *)
val ast_iter : ('p Core.Expr.at -> unit) -> 'p Core.Expr.at -> unit

(** Check if a de Bruijn index occurs in a term.
    @param k the de Bruijn index to look for (1-based, relative to [t])
    @param t the term to search
    @return [true] if [Core.Expr.Bound_variable k] appears free in [t] *)
val ast_occurs : int -> 'p Core.Expr.at -> bool

(** How many times [Core.Expr.Bound_variable 1] is read on the path through [a] that reads it
    most: a match counts its most-reading branch, not their sum. *)
val nb_occur_match : 'p Core.Expr.at -> int

(** Check if any de Bruijn index in the interval [[k, k']] occurs in a term.
    @param k  lower bound of the index range (inclusive)
    @param k' upper bound of the index range (inclusive)
    @param t  the term to search
    @return [true] if some [Core.Expr.Bound_variable i] with [k <= i <= k'] appears free in [t] *)
val ast_occurs_itvl : int -> int -> 'p Core.Expr.at -> bool

(** [ast_iter_rel_applied f t] calls [f n i args] on every [Core.Expr.Bound_variable i] in [t],
    with [n] the number of bindings crossed to reach it and [args] the
    arguments it is applied to there ([[]] where it is not applied). *)
val ast_iter_rel_applied : (int -> int -> 'p Core.Expr.at list -> unit) -> 'p Core.Expr.at -> unit

(** Lift de Bruijn indices in a term.
    @param k the amount to add to each free de Bruijn index in [t]
    @param t the term whose free indices are to be lifted *)
val ast_lift : int -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Pop the outermost de Bruijn level (equivalent to [ast_lift (-1)]). *)
val ast_pop : 'p Core.Expr.at -> 'p Core.Expr.at

(** The number of nodes of a term, each counted once. *)
val ast_size : 'p Core.Expr.at -> int

(** Whether [a] and [b] are one read of storage: the same variable, or the
    same projection of the same such read.  Evaluating either is total and
    pure, so both evaluate to one value. *)
val same_storage : 'p Core.Expr.at -> 'p Core.Expr.at -> bool

(** [con_in_file file label]: the constant [label] of the library [file]
    ([Corelib.Init.Nat]), as its canonical name. *)
val con_in_file : string -> string -> Constant.t

(** [con_in_module file modname label]: the constant [label] of the module
    [modname] of the library [file]. *)
val con_in_module : string -> string -> string -> Constant.t

(** [canonical_app f args], [f] and [args] canonical: the canonical form of
    [Core.Expr.Apply (f, args)], read whole: a global applied in stages is applied once
    to every argument, a coercion of the head is dropped, and applying a
    one-branch match applies its branch.  No head of a canonical application
    is a global already applied, a coercion, or a match with one branch.
    See {!Core_passes.Spines}. *)
val canonical_app : 'p Core.Expr.at -> 'p Core.Expr.at list -> 'p Core.Expr.at

(** [canonical e] is [e] with every application canonical
    ({!canonical_app}). *)
val canonical : 'p Core.Expr.at -> 'p Core.Expr.at

(** [permut_rels k k' c] exchanges two adjacent runs of binders: [Rel 1 ...
    Rel k] become [Rel (k'+1) ... Rel (k'+k)], and [Rel (k+1) ... Rel (k+k')]
    become [Rel 1 ... Rel k']. *)
val permut_rels : int -> int -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Substitute a term for de Bruijn index 1, adjusting other indices.
    @param e the term to substitute for [Rel 1]
    @param t the term in which the substitution is performed *)
val ast_subst : 'p Core.Expr.at -> 'p Core.Expr.at -> 'p Core.Expr.at

(** [ast_subst_each make t] substitutes for each read of [Rel 1] in [t] a
    term of its own, [make ()], as {!ast_subst} substitutes one: a use of a
    global made for each read is an occurrence of its own, where one term
    copied to every read would make them all the same occurrence. *)
val ast_subst_each : (unit -> 'p Core.Expr.at) -> 'p Core.Expr.at -> 'p Core.Expr.at

(** Substitute global references in a term using the given map.
    @param s a map from [GlobRef.t] to replacement [Core.Expr.t] bodies
    @param t the term in which to perform the substitution *)
val ast_glob_subst : Core.Expr.extracted Core.Ref.User.Map.t -> Core.Expr.extracted -> Core.Expr.extracted

(** Remove unused variable bindings from a term. *)
val dump_unused_vars : 'p Core.Expr.at -> 'p Core.Expr.at

(** [branch_type_applied n ty] is the result type of a match branch whose
    value, of type [ty], has been applied to [n] arguments: [ty] with [n]
    arrows taken off, or [ty] itself when it has fewer. *)
val branch_type_applied : int -> 'p Core.Type.at -> 'p Core.Type.at

(** Normalize a Core term by beta-reduction and simplification. *)
val normalize : 'p Core.Expr.at -> 'p Core.Expr.at

(** [apply_eta_args f args] is [f] applied to [args], with the application
    placed where [f] produces its value rather than wrapped around [f] -- for
    callers that build an application after simplification has already run,
    such as eta-expansion to a declaration's arity.  The result is
    canonical ({!canonical}), as every term built after
    {!Core_passes.Spines.structure} must be. *)
val apply_eta_args : 'p Core.Expr.at -> 'p Core.Expr.at list -> 'p Core.Expr.at

(** Optimize fixpoint expressions. *)
val optimize_fix : 'p Core.Expr.at -> 'p Core.Expr.at

(** Determine if a global reference should be inlined in the given term.
    @param r the global reference of the constant to test
    @param t the current extracted body of [r]
    @return [true] if [r] should be inlined at call sites *)
val inline : GlobRef.t -> 'p Core.Expr.at -> bool

(** Check if a pattern is a basic (non-nested) pattern. *)
val is_basic_pattern : Core.Pattern.t -> bool

(** Check if any branch has a deep (nested) pattern. *)
val has_deep_pattern : 'p Core.Match.Branch.at array -> bool

(** Check if a match is regular (all patterns are basic). *)
val is_regular_match : 'p Core.Match.Branch.at array -> bool

(** Exception raised when an operation is impossible. *)
exception Impossible

(** {2 Classification of signatures} *)

(** Classification of signatures based on their contents. *)
type sign_kind =
  | EmptySig  (** the empty signature *)
  | NonLogicalSig  (** at least a [Core.Signature.Argument.Runtime] *)
  | SafeLogicalSig  (** only [Core.Signature.Argument.Erased Core.Erasure_reason.Type_argument] *)
  | UnsafeLogicalSig  (** no [Core.Signature.Argument.Runtime], not all [Core.Signature.Argument.Erased
                          Core.Erasure_reason.Type_argument] *)

(** Classify a signature into one of the sign_kind categories.
    @return [EmptySig] for an empty list; [NonLogicalSig] if any [Core.Signature.Argument.Runtime] is
            present; [SafeLogicalSig] if all entries are
            [Core.Signature.Argument.Erased Core.Erasure_reason.Type_argument];
            [UnsafeLogicalSig] otherwise *)
val sign_kind : Core.Signature.t -> sign_kind

(** Remove the trailing [Runtime] entries from a signature. *)
val sign_no_final_keeps : Core.Signature.t -> Core.Signature.t

(** Remap type variable indices in a term using the given function.
    @param f   a function from old type variable index to new index; applied to
               every [Core.Type.Variable] annotation occurring in the term
    @param t   Core in which to remap type variable indices *)
val remap_tvars : (int -> int) -> 'p Core.Expr.at -> 'p Core.Expr.at
