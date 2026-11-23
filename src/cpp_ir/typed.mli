(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A lowered expression with the type lowering synthesised for it.  The
    record is private: a typed value is built only with a type, through
    {!v} or one of the synthesis rules here, so a lowering module that
    hands one on has said what it holds.

    The rules here read only the node: they cover the forms that carry
    their type ({!of_node}).  A variable, a global named as a value, and a
    call whose callee lowering knows are typed by the lowering module that
    builds them, which knows the binder or the declaration. *)

type t = private {
  expr : Lowered.Expr.t;
  ty : Lowered.Value_type.t;
}

(** [v ~ty e] is [e] of type [ty]. *)
val v : ty:Lowered.Value_type.t -> Lowered.Expr.t -> t

(** [typed t e] is [e] of exactly the nameable type [t]. *)
val typed : Lowered.Type.t -> Lowered.Expr.t -> t

(** [of_node ~fallback e] is [e] at the type its outermost node carries
    ({!carried}), and at [fallback], the type its builder knows, where the
    node carries none. *)
val of_node : fallback:Lowered.Value_type.t -> Lowered.Expr.t -> t

(** [Deduced Unannotated]: the type of a node built without one. *)
val unannotated : Lowered.Value_type.t

(** How a coercion expands ({!Cpp_passes.Coercions.expand}, which installs
    itself here: the expansion builds with finishing's vocabulary, which
    this module may not read). *)
val expansion : (Lowered.Coercion.plan -> Lowered.Expr.t -> Lowered.Expr.t) ref

(** [head e]: [e] as its outermost coercions expand it, for a decision that
    reads the form of the value it adapts. *)
val head : Lowered.Expr.t -> Lowered.Expr.t

(** The type [e]'s outermost node carries, a coercion's what it expands
    to: a cast, a box, a conversion, a call stating what it yields, an
    abort, a lambda whose grouping its parameters and returns say, foreign
    text, a runtime helper, a requirement.  [None] for a node that carries
    none (a variable, a global, a member, a call without its yield). *)
val carried : Lowered.Expr.t -> Lowered.Value_type.t option

(** [rewrap f x] is [f x.expr] at [x]'s type: for a rewrite that does not
    change what the value is, such as recording the Core occurrence it is
    made of. *)
val rewrap : (Lowered.Expr.t -> Lowered.Expr.t) -> t -> t

(** [applied f n] is what a callable of type [f] yields given [n]
    arguments in a call, taken group by group as its type takes them, as
    {!apply} takes them: a leading empty group is the call itself; the rest
    of a group they straddle and the groups after it, a function of what is
    left; past its last group, the result's own groups.  [None] where [f] or
    a result the arguments reach is no callable. *)
val applied : Lowered.Value_type.t -> int -> Lowered.Value_type.t option

(** [apply ?first ?prefix f args] is [f] applied to [args], in source order,
    as its type groups its parameters: one C++ call per group.  A group the
    arguments straddle at the end leaves a closure over the rest of it, its
    parameters named [prefix] (default ["_sat"]) and a position.  Arguments
    past [f]'s last group apply to its result, group by group at the
    result's own type; all at once where that is no callable, or [f]'s type
    gives no grouping (the call then {!unannotated}).  [first] builds the call of the first group in place of
    calling [f.expr] (a callee that takes more than the arguments, such as a
    lifted function's captured variables); a callee given [first] is called
    even with no arguments.  No arguments is [f] itself otherwise. *)
val apply : ?first:(Lowered.Expr.t list -> Lowered.Expr.t) -> ?prefix:string -> t -> Lowered.Expr.t list -> t

(** The value category of [x], from its node: a variable is an lvalue,
    [const] where its type is, a move an xvalue, anything else a
    prvalue. *)
val category : t -> Grammar.Value_category.t

(** [deduced ?binder x] declares an [auto] variable initialised with [x],
    recording [x]'s type ({!Grammar.Binding.Declare_deduced}). *)
val deduced : ?binder:Core.Binder.t -> t -> Grammar.lowered Grammar.Binding.t

(** [deduced_of_node ?binder e]: {!deduced} for an initialiser built
    without a typed value, at the type its node carries ({!carried}), or
    {!unannotated}. *)
val deduced_of_node : ?binder:Core.Binder.t -> Lowered.Expr.t -> Grammar.lowered Grammar.Binding.t

(** [bind_deduced ?binder x e] is [auto x = e;], [e]'s type recorded as
    {!deduced_of_node} records it. *)
val bind_deduced : ?binder:Core.Binder.t -> Names.Id.t -> Lowered.Expr.t -> Lowered.Stmt.t

(** [bind ?binder x t e] is [t x = e;], {!bind_deduced} where [t] is
    [auto]: how every lowered declaration whose type is computed is built,
    so that no lowered [Declare (Auto, _)] is left. *)
val bind : ?binder:Core.Binder.t -> Names.Id.t -> Lowered.Type.t -> Lowered.Expr.t -> Lowered.Stmt.t
