(** Found by Ephyra round 24, fixed. A case expression (an [if] or a
    [match]) passed as an argument, or applied as a callee, is lowered to an
    immediately invoked lambda (printed as a conditional expression), and
    the typed-fit check under [CRANE_CHECK_IR] put each branch's value in
    the slot of the return type of the enclosing function -- the method's,
    the local fixpoint's, the constructor's caller -- rather than in the
    lambda's own.  The C++ was right; extraction failed.  The branches now
    return to the lambda's own result ([Match.iife_return]), and the lambda
    as a whole is checked at the argument.

    - [via_method]: [sz (if b then Leaf else Node Leaf 0 Leaf)], a type
      class method; was "a value of type tree put in a slot of type nat".
    - [via_local_fix]: a local [fix] applied to a [match]; was "list bool put
      in a slot of type list (nat -> nat)".
    - [via_record]: a record constructor with a [match] field; was "list nat
      put in a slot of type r3".
    - [via_eta_fix]: a local [fix] returning [nat -> nat] whose body is a
      [match] of closures, eta-extended so the [match] is applied to the
      extra argument; was "closure put in a slot of type nat".

    Expected: extracts under [CRANE_CHECK_IR]; [via_method true = 1],
    [via_method false = 2], [via_local_fix 0 = 0], [rb (via_record []) = []],
    [rb (via_record [true]) = [1]], [via_eta = 3]. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Corelib Require Import PrimString.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module TypedFitCaseArgument.

Inductive tree : Type := Leaf | Node (l : tree) (v : nat) (r : tree).

Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_tree : Sz tree :=
  { sz t := match t with Leaf => 1 | _ => 2 end }.

Definition via_method (b : bool) : nat := sz (if b then Leaf else Node Leaf 0 Leaf).

Definition via_local_fix (n : nat) : nat :=
  List.length
    (let fix go (l : list bool) (acc : list (nat -> nat)) {struct l} : list (nat -> nat) :=
       match l with [] => acc | _ :: r => go r acc end
     in go (match n with O => [] | S _ => [true] end) []).

Record r3 : Type := mkr3 { ra : nat; rb : list nat; rc : bool }.

Definition via_record (l : list bool) : r3 :=
  mkr3 0 (match l with [] => [] | _ => [1] end) true.

Definition via_record_len (l : list bool) : nat := List.length (rb (via_record l)).

Definition via_eta : nat :=
  let cf :=
    (let fix go (l : list PrimString.string) (acc : nat -> nat) {struct l} : nat -> nat :=
       match l with [] => (fun _ => 0) | _ :: _ => acc end
     in go ["a"%pstring] (fun x => x))
  in cf 1 + cf 2.

Definition plain_f (t : tree) : nat := match t with Leaf => 1 | _ => 2 end.
Definition plain (b : bool) : nat := plain_f (if b then Leaf else Node Leaf 0 Leaf).

End TypedFitCaseArgument.

Crane Extraction "typed_fit_case_argument" TypedFitCaseArgument.
