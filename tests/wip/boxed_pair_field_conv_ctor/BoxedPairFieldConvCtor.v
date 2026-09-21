(** A converting constructor rebuilds a [shared_ptr]-boxed [std::pair] field.

    A constructor field that mentions the inductive being defined is held
    behind a [shared_ptr], and the converting constructor rebuilds it by
    handing the pointee straight to [make_shared] at the destination type:

        this->v_ = ENEG{v_0 ? std::make_shared<std::pair<T, Exp0<T>>>(
                                  deref v_0)
                            : nullptr};

    For a boxed field whose type is another Crane inductive that works, because
    the pointee type has a converting constructor of its own.  For a boxed
    [std::pair] it does not -- [std::pair]'s own converting constructor asks
    each component to be constructible from the other's, and an erased
    component is not.

    This is the same hole the direct-field case closed, on the path that does
    not ask the conversion helper: the boxed path allocates first and converts
    never.  [ESELF] is the control -- a boxed field whose pointee type converts
    on its own -- and it sits in the same converting constructor. *)

From Crane Require Import Mapping.Std.

Inductive dt : Set := | DI : nat -> dt | DP : dt.

Inductive exp (T : Set) : Set :=
  | EV : T -> exp T
  | ESELF : exp T -> exp T
  | ENEG : (T * exp T)%type -> exp T.
Arguments EV {T}. Arguments ESELF {T}. Arguments ENEG {T}.

Definition depth (T : Set) (e : exp T) : nat :=
  match e with EV _ => 1 | ESELF _ => 2 | ENEG _ => 3 end.
Arguments depth {T}.

Definition run (e : exp dt) : nat := depth e.

Crane Extraction "boxed_pair_field_conv_ctor" run.
