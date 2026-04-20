From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module SimpleLambdaFieldCapture.

(** Control test: a SIMPLE lambda (not a local fixpoint) captures
    pattern variables from a match on a value-type inductive.

    Simple lambdas should use [=] capture, so this SHOULD be safe.
    If this test fails, it means even simple lambdas have the
    dangling capture bug. *)

Inductive mylist : Type :=
  | mynil : mylist
  | mycons : nat -> mylist -> mylist.

Fixpoint mylist_sum (l : mylist) : nat :=
  match l with
  | mynil => 0
  | mycons h t => h + mylist_sum t
  end.

(** A second inductive to prevent methodification. *)
Inductive tag : Type :=
  | MkTag : nat -> tag.

(** Simple lambda captures [h] and [t] from match.
    Should use [=] capture (safe). *)
Definition head_adder (l : mylist) : option (nat -> nat) :=
  match l with
  | mynil => None
  | mycons h t => Some (fun x => x + h + mylist_sum t)
  end.

(** test1: l = [10, 20, 30], h=10, t=[20,30], mylist_sum(t)=50.
    f(5) = 5 + 10 + 50 = 65. *)
Definition test1 : nat :=
  match head_adder (mycons 10 (mycons 20 (mycons 30 mynil))) with
  | Some f => f 5
  | None => 999
  end.

(** test2: With noise to clobber stack.
    l = [100, 200], h=100, t=[200], mylist_sum(t)=200.
    f(0) = 0 + 100 + 200 = 300. *)
Definition test2 : nat :=
  let opt := head_adder (mycons 100 (mycons 200 mynil)) in
  let noise := mylist_sum (mycons 1 (mycons 2 (mycons 3 mynil))) in
  match opt with
  | Some f => f 0
  | None => noise
  end.

(** Dummy use of tag. *)
Definition mk_tag (n : nat) : tag := MkTag n.

End SimpleLambdaFieldCapture.

Crane Extraction "simple_lambda_field_capture" SimpleLambdaFieldCapture.
