(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A constant's MiniML type scheme, with the layout of the source binders
    its variables come from.

    The body mentions [Tvar 1 .. Tvar (arity)]; {!Scheme.Var.of_tvar} names
    them.  The layout has one entry per binder of the declaration's Rocq
    product spine, in source order -- value and proof binders included, so a
    call's arguments walk it in lockstep with no projection to a "type-level"
    sublist.  A binder's role (whether a call passes an argument for it) and
    its variable are independent facts: a proof binder has no variable, an
    erased family binder may have none, and a configured implicit has one
    exactly when type extraction gave it one. *)

(** Whether a call passes an argument for a binder. *)
type binder_role =
  | Value  (** a call passes an argument *)
  | Erased of Miniml.kill_reason  (** erased, for this reason; no argument *)

(** One binder of the layout. *)
type binder_info = {
  binder : Scheme.Binder.t;  (** its position in the product spine *)
  role : binder_role;
  scheme_var : Scheme.Var.t option;  (** the scheme variable it binds, if any *)
}

(** One binder as type extraction met it: the kill reason its domain was
    extracted with, if erased, and the provisional variable number it was
    given, if it was a type binder. *)
type raw_binder = {
  raw_erased : Miniml.kill_reason option;
  raw_tvar : int option;
}

(** A scheme: a fresh identity, a body and a binder layout. *)
type t

(** The largest schematic variable [ty] mentions, [0] if none. *)
val max_tvar : Miniml.ml_type -> int

(** [make owner body layout] finalizes a scheme: every binder [layout]
    numbers is a variable, whether or not [body] mentions it -- the scheme
    quantifies what the source quantifies, and which of those survive into
    the body is a fact about the body -- and the identity is fresh.  Raises
    [Invalid_argument] if two binders claim one variable. *)
val make : Names.GlobRef.t -> Miniml.ml_type -> raw_binder list -> t

(** The scheme's identity, fresh at {!make}. *)
val id : t -> Scheme.Id.t

(** The constant whose type it is. *)
val owner : t -> Names.GlobRef.t

(** The type, its variables [Tvar 1 .. Tvar (arity)]. *)
val body : t -> Miniml.ml_type

(** The number of variables it quantifies. *)
val arity : t -> int

(** Its variables, in order. *)
val vars : t -> Scheme.Var.t list

(** The layout: one entry per source binder, in source order. *)
val binders : t -> binder_info list

(** The layout entry at binder position [b]. *)
val binder : t -> Scheme.Binder.t -> binder_info option

(** The binder variable [v] comes from, if a binder of the layout has it. *)
val origin : t -> Scheme.Var.t -> binder_info option

(** [with_roles f s] is the view of [s] whose binder roles are [f info]:
    configured implicits and conservative types are applied by the caller,
    which can read the configuration, without touching variable origins. *)
val with_roles : (binder_info -> binder_role) -> t -> t

(** Replaces the body with an equivalent spelling (an expansion of its
    abbreviations), keeping the identity and the layout. *)
val with_body : Miniml.ml_type -> t -> t

(** The scheme's invariants, as a list of violations: the body names no
    variable past the arity, every variable has exactly one source binder,
    and the layout is in source order, names only this scheme's variables
    and gives no variable to two binders. *)
val validate : t -> string list
