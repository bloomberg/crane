From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module PairSelfDeepCopy.

(** Like the [option] case, but the recursive occurrence is hidden under
    [prod].  The generated C++ currently represents the field as an owned
    [std::pair] containing an owned recursive value.  Clone generation then
    emits invalid C++ that calls [.clone()] on the [std::pair] object itself, so
    this test fails at C++ compile time. *)

Inductive chain : Type :=
| Stop : chain
| Link : chain * bool -> chain.

Definition dup_chain (c : chain) : chain * chain := (c, c).

End PairSelfDeepCopy.

Crane Extraction "pair_self_deep_copy" PairSelfDeepCopy.
