From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint whose result type is a function type behind a
    definition ([st A := nat -> A * nat], a state monad), applied by an
    observer: the fixpoint is eta-expanded to return [std::pair<..>] but its
    branches return [st<..>] ([crane::fn]) values: "no viable conversion from
    returned value of type 'st<unsigned long long>' to 'std::pair<..>'".  The
    literal-arrow forms (local_fix_returns_function,
    local_fix_function_result_inlined) are fixed. *)
Module LocalFixAliasFunctionResult.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Definition t : nat :=
  (fun w : st nat => fst (w 3))
  (let fix go (l : list bool) (acc : st nat) {struct l} : st nat :=
     match l with [] => sret 7 | _ :: _ => sret 9 end in go [] (sret 1)).

End LocalFixAliasFunctionResult.

Crane Extraction "local_fix_alias_function_result" LocalFixAliasFunctionResult.
