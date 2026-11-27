(** Found by Ephyra round 28. A [match] whose branches are [sig]s of a
    function ([{f : nat -> nat | True}], the witness under
    [Mapping.Shared]): one branch [exist _ (fun _ => 1) I], the other the
    result of a call ([pick h k1 k2 0]). The match became an immediately
    invoked C++ lambda with no declared return type, returning a bare lambda
    in one branch and a [crane::fn<uint64_t(uint64_t)>] in the other
    ("return type 'crane::fn<...>' must match previous return type
    '(lambda ...)'"). Over plain [nat -> nat] the branches were joined at
    [crane::fn].

    Fixed: the join asked whether the branches' type is a function type of
    its C++ spelling as written, [sig<fn(nat) -> nat>], which is not one; it
    now asks it of the type with aliases and component mappings unfolded
    ([Match_types.declared_at], [Coerce.aliases_in]), so the lambda is
    declared at the witness's [crane::fn].

    Expected: compiles, [result = 1]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
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
