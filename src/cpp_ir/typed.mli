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

(** The type [of_node] reads off [e]'s outermost node. *)
val node_type : Lowered.Expr.t -> Lowered.Value_type.t

(** [rewrap f x] is [f x.expr] at [x]'s type: for a rewrite that does not
    change what the value is, such as recording the Core occurrence it is
    made of. *)
val rewrap : (Lowered.Expr.t -> Lowered.Expr.t) -> t -> t

(** [x], typed as [ty] where it is not yet typed. *)
val or_type : Lowered.Value_type.t -> t -> t

(** The value category of [x], from its node: a variable is an lvalue,
    [const] where its type is, a move an xvalue, anything else a
    prvalue. *)
val category : t -> Grammar.Value_category.t
