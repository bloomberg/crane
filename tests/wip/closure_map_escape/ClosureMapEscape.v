From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureMapEscape.

Inductive mylist (A : Type) : Type :=
  | mynil : mylist A
  | mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} _ _.

(** Build a list of closures from a list of nats using LOCAL FIXPOINTS.
    Each recursive call creates a fixpoint [add] that captures the
    pattern variable [h] from the match.

    BUG: Each local fixpoint uses [&] capture. The pattern variable [h]
    is a local binding within the match IIFE. The fixpoint is stored in
    [mycons] (a constructor), so [return_captures_by_value] does NOT
    apply. After the match, [h] goes out of scope, and the closure
    references dangling memory.

    Difference from fix_escape_match: uses a USER-DEFINED list type
    (not stdlib option), and the fixpoints are built RECURSIVELY
    from list elements (not a single fixpoint). *)

Fixpoint map_to_adders (l : mylist nat) : mylist (nat -> nat) :=
  match l with
  | mynil => mynil
  | mycons h t =>
    let fix add (x : nat) : nat :=
      match x with
      | O => h
      | S x' => S (add x')
      end
    in mycons add (map_to_adders t)
  end.

Fixpoint apply_first (fns : mylist (nat -> nat)) (arg : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f _ => f arg
  end.

Fixpoint sum_apply (fns : mylist (nat -> nat)) (arg : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f rest => f arg + sum_apply rest arg
  end.

(** test1: map_to_adders [10, 20, 30], apply first to 5.
    add(5) where add(x) = x + 10. So 10 + 5 = 15.
    Bug: h=10 captured by [&], dangling after match. *)
Definition test1 : nat :=
  apply_first (map_to_adders (mycons 10 (mycons 20 (mycons 30 mynil)))) 5.

(** test2: Sum of applying all adders to 0.
    (0+10) + (0+20) + (0+30) = 60. *)
Definition test2 : nat :=
  sum_apply (map_to_adders (mycons 10 (mycons 20 (mycons 30 mynil)))) 0.

(** test3: Build adders, noise, then apply.
    (1+100) + (1+200) = 302. *)
Definition test3 : nat :=
  let fns := map_to_adders (mycons 100 (mycons 200 mynil)) in
  let noise := 1 + 2 + 3 in
  sum_apply fns 1.

End ClosureMapEscape.

Crane Extraction "closure_map_escape" ClosureMapEscape.
