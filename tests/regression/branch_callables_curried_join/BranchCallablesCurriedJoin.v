From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Match branches producing two-argument function values, one a curried
    lambda, the other a composed let-lambda ([let cf .. in let cg .. in fun c
    => cf (cg c)]), bound by a beta-redex: the C++ declares the variable at
    one branch's type and assigns the other ("no viable overloaded '='").
    Remaining after d7cf5aaae (common crane::fn type for joined callables).
    A match's branches now carry the slot into their tails, so the lambda
    knows the Core type backing the two-parameter function it is written
    against, and takes the parameter its body leaves to a partial
    application. *)
Module BranchCallablesCurriedJoin.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition t (l : list nat) : nat :=
  (fun w : nat -> pt -> bool => if w 0 (mkpt 0 true) then 1 else 2)
  (match List.length l with
   | O => (fun _ : nat => (fun _ : pt => true))
   | S _ => (let cf := (fun _ : bool => (fun _ : pt => false)) in
             let cg := (fun _ : nat => true) in fun c : nat => cf (cg c))
   end).

(** The same join as a [fold_left] step's result: the accumulator passes
    through [fold_left]'s type variable, so the step returns its curried
    spelling, and so do both branches. *)
Definition t2 (l : list nat) : nat :=
  (fold_left (fun (acc : Z -> bool -> nat) (x : nat) =>
     match x with
     | O => (fun _ : Z => (fun b : bool => if b then 1 else 0))
     | S _ => (let cf := (fun (n : nat) (_ : bool) => n) in fun z : Z => cf (acc z false))
     end) l (fun _ _ => 7)) 3%Z true.

End BranchCallablesCurriedJoin.

Crane Extraction "branch_callables_curried_join" BranchCallablesCurriedJoin.
