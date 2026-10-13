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

type binder_role =
  | Value
  | Erased of Miniml.kill_reason

type binder_info = {
  binder : Scheme.Binder.t;
  role : binder_role;
  scheme_var : Scheme.Var.t option;
}

(** One binder as type extraction met it: the kill reason its domain was
    extracted with, if erased, and the provisional variable number it was
    given, if it was a type binder. *)
type raw_binder = {
  raw_erased : Miniml.kill_reason option;
  raw_tvar : int option;
}

type t

(** The largest schematic variable [ty] mentions, [0] if none. *)
val max_tvar : Miniml.ml_type -> int

(** [make owner body layout] finalizes a scheme: its arity is the largest
    variable [body] mentions, a binder numbered past it gets no variable, and
    the identity is fresh.  Raises [Invalid_argument] if two binders claim
    one variable. *)
val make : Names.GlobRef.t -> Miniml.ml_type -> raw_binder list -> t

val id : t -> Scheme.Id.t
val owner : t -> Names.GlobRef.t
val body : t -> Miniml.ml_type
val arity : t -> int
val vars : t -> Scheme.Var.t list
val binders : t -> binder_info list
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

(** The schema invariants of section 8.1, as a list of violations: variables
    dense and owned, binder mappings source-ordered, in range and unique. *)
val validate : t -> string list
