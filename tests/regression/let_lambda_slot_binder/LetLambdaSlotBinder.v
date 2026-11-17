From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    The argument of a beta-redex [(fun w : bool -> nat => ...) (let cf := fun _ : tree => 1 in
    fun c : bool => cf Leaf)] binds [w] and then [cf]; the C++ lambda for [cf]
    takes its parameter type from [w]'s domain ([bool]) instead of its own
    binder ([tree]), so [crane::fn<uint64_t(tree)> cf = [](bool) {...}] does
    not compile.  With a domain that converts implicitly (e.g. [nat] into
    [std::optional]) the wrong type compiles silently. *)
Module LetLambdaSlotBinder.

Inductive tree : Type := Leaf : tree | Node : tree -> tree.

Definition t : nat :=
  (fun w : bool -> nat => w true + w false)
    (let cf := (fun _ : tree => 1) in fun c : bool => cf Leaf).

End LetLambdaSlotBinder.

Crane Extraction "let_lambda_slot_binder" LetLambdaSlotBinder.
