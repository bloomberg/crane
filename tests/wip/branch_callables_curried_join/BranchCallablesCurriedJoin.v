From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Match branches producing two-argument function values, one a curried
    lambda, the other a composed let-lambda ([let cf .. in let cg .. in fun c
    => cf (cg c)]), bound by a beta-redex: the C++ declares the variable at
    one branch's type and assigns the other ("no viable overloaded '='").
    Remaining after d7cf5aaae (common crane::fn type for joined callables). *)
Module BranchCallablesCurriedJoin.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition t (l : list nat) : nat :=
  (fun w : nat -> pt -> bool => if w 0 (mkpt 0 true) then 1 else 2)
  (match List.length l with
   | O => (fun _ : nat => (fun _ : pt => true))
   | S _ => (let cf := (fun _ : bool => (fun _ : pt => false)) in
             let cg := (fun _ : nat => true) in fun c : nat => cf (cg c))
   end).

End BranchCallablesCurriedJoin.

Crane Extraction "branch_callables_curried_join" BranchCallablesCurriedJoin.
