(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an instance whose class arguments mention its own type
    variable in more than one position gets a method signature substituted
    twice.  For [Instance unw {A} : Conv (wrap A) A], the class's [A] maps to
    [wrap A'] and its [B] to [A'], but the substitutions are applied one
    after the other over a shared variable numbering, so [B] -> [A'] is then
    rewritten again by [A] -> [wrap A'], and the method is emitted as
    [wrap<T1> conv(wrap<T1>)].  Its body returns the unwrapped value: "no
    viable conversion from returned value of type 'const unsigned long long'
    to function return type 'wrap<unsigned long long>'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module InstanceTvarSubstitutionOrder.

Class Conv (A B : Type) := { conv : A -> B }.

Inductive wrap (A : Type) := W : A -> wrap A.
Arguments W {A}.

#[export] Instance unw {A} : Conv (wrap A) A :=
  { conv := fun w => match w with W a => a end }.

Definition result : nat := conv (W 3).

End InstanceTvarSubstitutionOrder.

Crane Extraction "instance_tvar_substitution_order" InstanceTvarSubstitutionOrder.
