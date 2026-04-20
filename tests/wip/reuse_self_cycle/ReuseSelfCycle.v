From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseSelfCycle.

(** mycons at index 0 so reuse fires on the mycons branch. *)

Inductive mylist : Type :=
  | mycons : nat -> mylist -> mylist
  | mynil : mylist.

Arguments mycons _ _.
Arguments mynil.

Fixpoint length (l : mylist) : nat :=
  match l with
  | mycons _ xs => 1 + length xs
  | mynil => 0
  end.

(** BUG: The reuse optimization fires and sets [d_a1 = l], where [l]
    is the scrutinee (the very node being mutated).
    This creates a CYCLE: the node's tail points to itself.

    In Rocq, [mycons x l] creates a FRESH cons cell whose tail is [l].
    With reuse, the SAME cell is mutated: [d_a1 <- l] makes the cell
    point to itself.

    Calling [length] on the result causes infinite recursion -> stack overflow.

    Reuse fires because:
    1. [l] escapes in [else l] -> owned
    2. mycons branch tail is mycons with arity 2 = 2
    3. mycons is index 0 -> [List.hd] picks it
    4. [use_count() == 1] for fresh values *)

Definition prepend_self (l : mylist) (b : bool) : mylist :=
  if b then
    match l with
    | mycons x xs => mycons x l
    | mynil => mynil
    end
  else l.

(** test1: prepend_self([1, 2], true) should produce [1, 1, 2].
    In Rocq: mycons 1 (mycons 1 (mycons 2 mynil)), length = 3.
    With reuse bug: mycons 1 -> itself (cycle), length = infinite loop. *)
Definition test1 : nat :=
  length (prepend_self (mycons 1 (mycons 2 mynil)) true).

(** test2: Even simpler - single element list.
    prepend_self([42], true) should produce [42, 42], length = 2.
    With bug: [42] -> itself, length = infinite. *)
Definition test2 : nat :=
  length (prepend_self (mycons 42 mynil) true).

End ReuseSelfCycle.

Crane Extraction "reuse_self_cycle" ReuseSelfCycle.
