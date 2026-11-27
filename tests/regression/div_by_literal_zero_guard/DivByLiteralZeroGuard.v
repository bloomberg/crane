From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [Nat.div 0 0] in a polymorphic definition is not folded and prints
    [(0 ? 0 / 0 : 0)]; the dead [0 / 0] is rejected by clang's
    -Wdivision-by-zero under the suite's -Werror.  The value is right. *)
Module DivByLiteralZeroGuard.

Definition f {A : Type} (a : A) : nat := Nat.div 0 0 + Nat.modulo 5 0.

Definition t : nat := f true.

(** A literal [Nat.modulo 12 0] in a branch of a mutual fixpoint, which is
    not polymorphic. *)
Fixpoint ev (l : list nat) : nat :=
  match l with [] => Nat.modulo 12 0 | _ :: r => od r end
with od (l : list nat) : nat :=
  match l with [] => 0 | _ :: r => ev r end.

Definition t2 : nat := ev [1; 2].

End DivByLiteralZeroGuard.

Crane Extraction "div_by_literal_zero_guard" DivByLiteralZeroGuard.
