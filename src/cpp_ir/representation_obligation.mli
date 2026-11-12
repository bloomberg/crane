(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a lowered declaration may still owe resolution, and the printer
    must never be handed undecided: a type with no spelling, a callable
    parameter whose constraint the body has not settled, a cast whose caster
    is not chosen, a type variable nothing declares, a type argument a
    mapping's template names and its application leaves out, a call of a
    method or a projection written as a call of a function, a lambda invoked
    only to choose between two values, a member read of a moved object, a
    definition not yet known to be [constexpr] or not, a mapping's text not
    yet instantiated.

    Each is discharged by one resolution pass, and a resolved declaration
    owes none.  The list is closed: a new kind of debt the printer must not
    see is a new constructor here, with the pass that pays it. *)

type t =
  | Unresolved_type
      (** No pass determined a type, so no pass can discharge it; whatever
          wrote it owes it.  Stands at a type as {!Grammar.Type.Obligation}. *)
  | Opaque_type
      (** A type whose representation is not known here, settled where a
          type is written down.  Stands at a type as
          {!Grammar.Type.Obligation}. *)
  | Unspellable_binder
      (** a binder's type a custom match writes and C++ cannot spell *)
  | Unsettled_callable
      (** a callable parameter as its declaration types it
          ({!Grammar.Parameter_kind.Callable_declared}) *)
  | Unresolved_cast  (** an [any_cast] whose caster is still to choose *)
  | Free_type_variable  (** a type variable no enclosing head declares *)
  | Implicit_boxed_read
      (** a boxed value read where the context needs a concrete type, with
          no unboxing saying so *)
  | Missing_template_argument
      (** a type argument an inline mapping's template names and its
          application does not supply *)
  | Unlowered_method_call
  | Unlowered_projection
  | Unlowered_conditional
      (** a lambda invoked at once that only chooses between two values,
          not written as the conditional it computes *)
  | Move_under_access  (** a member read of a moved object *)
  | Undecided_constexpr
      (** a definition whose eligibility is {!Grammar.Constexpr.Undecided} *)
  | Uninstantiated_mapping
      (** an inline mapping whose text places its arguments, applied but not
          instantiated *)
  | Unlowered_qualifier
      (** a named type qualifying a member in value position, or a
          suspension, not yet spelled as a value *)
  | Unslotted_pointer
      (** a pointer whose slot -- a shared value's own handle, or the choice
          a functor's instantiation makes -- is not written down *)
  | Unnamed_scrutinee  (** a match reading a scrutinee no local holds *)
  | Undecided_capture
      (** a lambda whose capture is not written down: one that runs in place
          or one that is stored ({!Grammar.Capture}) *)
  | Capture_outside_a_block
      (** a variable initialised by an expression holding a lambda that
          captures, not invoked in place *)

(** Every obligation, in the order resolution discharges them. *)
val all : t list
