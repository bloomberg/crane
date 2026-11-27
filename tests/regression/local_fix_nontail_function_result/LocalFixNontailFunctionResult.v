From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint returning a function through a non-tail recursive call
    ([let rv := go r acc in if .. then (fun _ => Leaf) else rv]), in a match
    branch, called on a literal [[]]: under CRANE_CHECK_IR=1 "closure escape:
    the local fixpoint go escapes in its generated code but nowhere in Core".
    The tail-call shapes in local_fix_returns_function and
    local_fix_function_result_inlined are fixed.  Eta-expanded to the
    function's argument, [go r acc] is a partial application, whose closure
    holds [go]: escape analysis now counts one as an escape. *)
Module LocalFixNontailFunctionResult.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition g (t : tree) : (nat -> nat) -> tree :=
  match t with
  | Leaf => let fix go (l : list tree) (acc : (nat -> nat) -> tree) {struct l} : (nat -> nat) -> tree :=
              match l with
              | [] => (fun _ => Leaf)
              | _ :: r => let rv := go r acc in (if Nat.eqb 0 1 then (fun _ => Leaf) else rv)
              end
            in go [] (fun _ => Leaf)
  | Node _ _ _ => (fun _ => Leaf)
  end.

Definition t : bool := match g Leaf (fun x => x) with Leaf => true | Node _ _ _ => false end.

Record pt : Type := mkpt { px : nat; py : bool }.

(** Variants: the call in mutual fixpoints, through a second local fixpoint
    whose step returns its function accumulator, and with the outer
    fixpoint called inside the inner one's step. *)
Fixpoint h6a (n : nat) : tree -> list pt :=
  match n with
  | O => fun _ => []
  | S m =>
    let fix go (l : list nat) (acc : tree -> list pt) {struct l} : tree -> list pt :=
      match l with
      | [] => acc
      | x :: r =>
        let rv := go r acc in
        let fix go2 (l2 : list nat) (a2 : tree -> list pt) {struct l2} : tree -> list pt :=
          match l2 with [] => a2 | _ :: r2 => go2 r2 a2 end in
        go2 [x] rv
      end in
    go [1; 2] (h6b m)
  end
with h6b (n : nat) : tree -> list pt :=
  match n with O => fun _ => [mkpt 0 true] | S m => h6a m end.

Fixpoint k1 (n : nat) : tree -> list pt :=
  match n with
  | O => fun _ => []
  | S m =>
    let fix go (l : list nat) (acc : tree -> list pt) {struct l} : tree -> list pt :=
      match l with
      | [] => acc
      | x :: r =>
        let fix go2 (l2 : list nat) (a2 : tree -> list pt) {struct l2} : tree -> list pt :=
          match l2 with [] => go r a2 | _ :: r2 => go2 r2 a2 end in
        let rv := go2 [x] acc in
        if Nat.eqb x 7 then (fun _ => []) else rv
      end in
    go [1; 2] (k1 m)
  end.

Definition t2 : nat := List.length (h6a 3 Leaf) + List.length (k1 2 Leaf).

End LocalFixNontailFunctionResult.

Crane Extraction "local_fix_nontail_function_result" LocalFixNontailFunctionResult.
