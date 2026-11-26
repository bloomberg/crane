(** Found by Ephyra round 28. A [match] whose branches are [sig]s of a
    function ([{f : nat -> nat | True}], the witness under
    [Mapping.Shared]): one branch [exist _ (fun _ => 1) I], the other the
    result of a call ([pick h k1 k2 0]). The match becomes an immediately
    invoked C++ lambda with no declared return type, returning a bare lambda
    in one branch and a [crane::fn<uint64_t(uint64_t)>] in the other. With
    the same program over plain [nat -> nat] (no [sig]) the branches are
    joined at [crane::fn] and it compiles. Variant of
    [sig_closure_witness_fit] (the [sig] of a function not seen as its
    witness). Expected: compiles, [result = 1]. Actual: "return type
    'crane::fn<unsigned long long (unsigned long long)>' must match previous
    return type '(lambda ...)' when lambda expression has unspecified
    explicit return type". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module SigFnMatchJoin.

Definition pick {A : Type} (b : bool) (x y : A) : A := if b then x else y.
Definition result : nat :=
  (fun w : {f : nat -> nat | True} => proj1_sig w 0)
    (match pick true [] [true] with
     | [] => exist (fun _ : nat -> nat => True) (fun _ : nat => 1) I
     | h :: _ =>
         pick h (fun _ : nat => exist (fun _ : nat -> nat => True) (fun _ : nat => 2) I)
                (fun _ : nat => exist (fun _ : nat -> nat => True) (fun _ : nat => 3) I) 0
     end).

End SigFnMatchJoin.

Crane Extraction "sig_fn_match_join" SigFnMatchJoin.
