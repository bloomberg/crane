(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** The iterative destructor walks a recursive field to avoid deep recursion.
    For a field of type [option (t * nat)] the walk reads the pair component as
    [a0->first], applying [operator->] to the [std::optional] rather than
    opening it first.  A bare [option t] and a bare [t * t] both work, so it is
    the nesting the drain path does not handle. *)

Module DrainOptionPairField.

  Inductive t := C : option (t * nat) -> t.

  Fixpoint depth (x : t) : nat :=
    match x with
    | C o => match o with Some p => 1 + depth (fst p) | None => 0 end
    end.

  Definition test : nat := depth (C (Some (C None, 1))).

End DrainOptionPairField.

Crane Extraction "drain_option_pair_field" DrainOptionPairField.
