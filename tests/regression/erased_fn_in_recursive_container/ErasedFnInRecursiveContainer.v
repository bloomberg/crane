From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

(** The payload of a recursive polymorphic container is erased to [std::any] on
    the way in, but the read back at [option (nat -> nat)] is spelled as a
    plain functional cast rather than an unerasing one: "no matching conversion
    for functional-style cast from 'const std::function<std::any (std::any)>'
    to 'std::function<Nat (Nat)>'".  The same payload in a non-recursive
    container round-trips correctly. *)

Module ErasedFnInRecursiveContainer.
  Inductive rose (A : Type) := node : A -> list (rose A) -> rose A.
  Arguments node {A}.

  Fixpoint size (A : Type) (x : rose A) : nat :=
    match x with
    | node _ l => S (List.fold_left (fun a y => a + size A y) l 0)
    end.

  Definition run : nat :=
    size (option (nat -> nat)) (node (Some (fun x => x)) [node None []]).
End ErasedFnInRecursiveContainer.

Crane Extraction "erased_fn_in_recursive_container" ErasedFnInRecursiveContainer.
