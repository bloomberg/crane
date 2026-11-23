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

(** [untyped e] is [e], whose form lowering does not type yet. *)
val untyped : Lowered.Expr.t -> t

(** [of_node e] is [e] at the type its outermost node carries, or not yet
    typed where the node does not carry one. *)
val of_node : Lowered.Expr.t -> t

(** How a coercion expands ({!Cpp_passes.Coercions.expand}, which installs
    itself here: the expansion builds with finishing's vocabulary, which
    this module may not read). *)
val expansion : (Lowered.Coercion.plan -> Lowered.Expr.t -> Lowered.Expr.t) ref

(** [head e]: [e] as its outermost coercions expand it, for a decision that
    reads the form of the value it adapts. *)
val head : Lowered.Expr.t -> Lowered.Expr.t

(** The type [of_node] reads off [e]'s outermost node, a coercion's off
    what it expands to. *)
val node_type : Lowered.Expr.t -> Lowered.Value_type.t

(** [rewrap f x] is [f x.expr] at [x]'s type: for a rewrite that does not
    change what the value is, such as recording the Core occurrence it is
    made of. *)
val rewrap : (Lowered.Expr.t -> Lowered.Expr.t) -> t -> t

(** [x], typed as [ty] where it is not yet typed. *)
val or_type : Lowered.Value_type.t -> t -> t

(** [applied f n] is what a callable of type [f] yields given [n]
    arguments, taken group by group as its type takes them: the rest of a
    group they straddle and the groups after it, a function of what is left;
    past its last group, the result's own groups.  Not yet typed where [f]
    or a result the arguments reach is no callable. *)
val applied : Lowered.Value_type.t -> int -> Lowered.Value_type.t

(** [apply ?first ?prefix f args] is [f] applied to [args], in source order,
    as its type groups its parameters: one C++ call per group.  A group the
    arguments straddle at the end leaves a closure over the rest of it, its
    parameters named [prefix] (default ["_sat"]) and a position.  Arguments
    past [f]'s last group apply to its result, group by group at the
    result's own type; all at once where that is no callable, or [f]'s type
    is unknown.  [first] builds the call of the first group in place of
    calling [f.expr] (a callee that takes more than the arguments, such as a
    lifted function's captured variables); a callee given [first] is called
    even with no arguments.  No arguments is [f] itself otherwise. *)
val apply : ?first:(Lowered.Expr.t list -> Lowered.Expr.t) -> ?prefix:string -> t -> t list -> t

(** The value category of [x], from its node: a variable is an lvalue,
    [const] where its type is, a move an xvalue, anything else a
    prvalue. *)
val category : t -> Grammar.Value_category.t
