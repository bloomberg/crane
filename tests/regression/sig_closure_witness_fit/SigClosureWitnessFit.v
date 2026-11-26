(** Found by Ephyra round 28. With [Mapping.Shared]'s [sig] its witness, a
    [sig] whose witness is a function returning a non-scalar
    ([{f : bool -> list nat | True}]), built with [exist] from a lambda and
    passed to a function. The typed-fit check found the lambda, a
    [closure (bool) -> list nat], put in the [sig<fn(bool) -> list nat>]
    parameter (destination, unrelated). [result2]: a lambda whose result is
    such a [sig], as [hd_or]'s default, was refused the same way (argument,
    unrelated, fn <- closure). The C++ compiled and was right.

    Fixed: the coercion machinery unfolded aliases and zero-argument
    mappings but not a typed mapping whose C++ type is one of its
    components; it now reads such a type as that component ([sig A P] is
    [A], [Coerce.aliases_in]), so the closure is compared with the
    witness's function type.

    Expected: extracts under CRANE_CHECK_IR, [result = 31],
    [result2 = 5]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module SigClosureWitnessFit.

Definition use (w : {f : bool -> list nat | True}) : nat :=
  length (proj1_sig w true) * 10 + length (proj1_sig w false).
Definition result : nat :=
  use (exist (fun _ : bool -> list nat => True)
         (fun b : bool => if b then [1; 2; 3] else [4]) I).

(** The same as a function's result: a lambda returning a [sig] of a function,
    the default of [hd_or] (argument, unrelated, fn <- closure). *)
Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition result2 : nat :=
  length (proj1_sig (hd_or (fun k : nat => exist (fun _ : nat -> list nat => True) (fun n => repeat 0 (n + k)) I)
                           (@nil (nat -> {f : nat -> list nat | True})) 2) 3).

End SigClosureWitnessFit.

Crane Extraction "sig_closure_witness_fit" SigClosureWitnessFit.
