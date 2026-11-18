From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A cofixpoint whose parameter is unused ([CoFixpoint c1 (n : nat) :=
    sconst 0]), passed unapplied to [map], prints as the call [c1()]: "too
    few arguments to function call, single argument '_x' was not
    specified".  Naming a cofixpoint calls it only where it takes no
    parameters. *)
Module CofixUnusedParamAsValue.

CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).
CoFixpoint c1 (n : nat) : stream := sconst 0.

Definition t : nat := List.length (map c1 [1; 2]).

(** The same inside a [fold_left] step, at an empty list. *)
CoFixpoint c4 (n : nat) : stream := sconst 0.
Definition t2 : nat := fold_left (fun a (x : nat) => a + x + List.length (map c4 [])) [1; 2] 0.

End CofixUnusedParamAsValue.

Crane Extraction "cofix_unused_param_as_value" CofixUnusedParamAsValue.
