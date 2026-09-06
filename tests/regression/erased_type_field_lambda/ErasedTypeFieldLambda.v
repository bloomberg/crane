From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A record with a [Type] field erases its dependent fields to [std::any], so
    [pairs] is declared [List<pair<std::any, std::function<uint64_t(std::any)>>>].
    The producers are not erased to match: each element is built as a
    [pair<uint64_t, <concrete lambda>>], which does not convert, and the lambda
    body adds to a [std::any] besides. *)

Module ErasedTypeFieldLambda.

  Record slot := MkSlot { sty : Type ; pairs : list (sty * (sty -> nat)) }.

  Definition weigh (s : slot) : nat :=
    List.fold_left (fun a p => a + snd p (fst p)) (pairs s) 0.

  Definition slots : list slot :=
    [ MkSlot nat [(1, fun x => x); (2, fun x => x * 10)]
    ; MkSlot (list nat) [([1;2;3], @List.length nat)] ].

  Definition run : nat := List.fold_left (fun a s => a + weigh s) slots 0.

End ErasedTypeFieldLambda.

Crane Extraction "erased_type_field_lambda" ErasedTypeFieldLambda.
