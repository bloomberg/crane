From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module OptionalSelfDeepCopy.

(** Self-recursion hidden under [option] is not the direct field shape handled
    by the iterative clone/destructor generator.  Crane currently lowers the
    field to an owned [std::optional] containing an owned [chain], then emits
    invalid clone code that tries to call [.clone()] on the [std::optional]
    object itself.  The generated C++ does not compile. *)

Inductive chain : Type :=
| Stop : chain
| More : option chain -> chain.

Definition dup_chain (c : chain) : chain * chain := (c, c).

End OptionalSelfDeepCopy.

Crane Extraction "optional_self_deep_copy" OptionalSelfDeepCopy.
