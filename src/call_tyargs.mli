(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A call's reading of its callee's scheme variables, variable by variable,
    as call planning resolves it (docs/Type-Argument-Numbering-Refactor-Plan.md,
    section 3.2).

    It starts from what the use wrote: each variable is known -- the argument
    the source gave at its binder -- or a hole, either because nothing was
    written there or because what was written is no type extraction could
    read ([F : Type -> Type] passed as [list]).  The use's frozen solution is
    not consulted: translation knows things extraction did not -- the types
    its passes gave the call's value arguments, the head an applied variable
    meets in one of them, the result the call is expected at -- and a hole
    may be resolved from those.  Only a hole: a variable the use wrote keeps
    what it wrote, a resolution is never an erased placeholder, and every
    resolution says what it was read from.  A hole nothing resolves is left
    to C++ deduction by the template-application planner. *)

(** What a known variable's type was read from. *)
type evidence =
  | Written  (** The argument the use wrote at the variable's binder. *)
  | Argument_types
      (** The call's value arguments' types, matched against the callee's
          domains. *)
  | Argument_heads
      (** The head an applied variable meets in a value argument's type, or
          the type a class alias in a domain is applied at. *)
  | Expected_result
      (** The type the call's result is expected at, with the arguments'
          heads. *)
  | Eta_parameter
      (** The template parameter an eta-expanded partial application binds
          for a variable the call leaves open. *)

type t

(** The reading of [use]'s written arguments; empty for a monomorphic use. *)
val of_use : Miniml.global_use -> t

val callee : t -> Names.GlobRef.t

(** The callee's variables, in ordinal order. *)
val vars : t -> Scheme.Var.t list

(** Whether nothing is known of the variable. *)
val is_hole : t -> Scheme.Var.t -> bool

(** Whether the use wrote nothing at the variable's binder and nothing has
    resolved it since: a hole with no evidence at all, which C++ may only
    deduce. *)
val is_unwritten : t -> Scheme.Var.t -> bool

(** Every variable nothing is known of. *)
val holes : t -> Scheme.Var.t list

(** The holes before the last variable known or written unreadably: the
    ones {!by_variable} spells as erased placeholders. *)
val interior_holes : t -> Scheme.Var.t list

(** The variables after the last one known or written unreadably: the ones
    {!by_variable} leaves out. *)
val beyond_extent : t -> Scheme.Var.t list

(** [resolve e answer vs t] resolves each hole among [vs] for which [answer]
    gives a type that is no erased placeholder, as read from [e]. *)
val resolve :
  evidence -> (Scheme.Var.t -> Miniml.ml_type option) -> Scheme.Var.t list -> t -> t

(** {!resolve}, all or nothing: [t] itself unless every hole among [vs] is
    answered. *)
val resolve_all :
  evidence -> (Scheme.Var.t -> Miniml.ml_type option) -> Scheme.Var.t list -> t -> t

(** Whether some variable was resolved from [e]. *)
val resolved_from : evidence -> t -> bool

(** The reading as call planning substitutes with: each variable's type, up
    to the last variable known or written unreadably, a hole before it
    spelled [Tdummy Ktype] -- the erased placeholder the erasure filters
    leave to deduction. *)
val by_variable : t -> Mlutil.Var_types.t
