From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module PairClosureEscape.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Definition sum_values (t : tree) (x : nat) : nat :=
  match t with
  | Leaf => x
  | Node l v r =>
    match l with
    | Leaf => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => lv + x
      | Node _ rv _ => lv + rv + v + x
      end
    end
  end.

(** BUG: Partial application stored in fst of a pair (std::make_pair).
    return_captures_by_value doesn't handle lambdas inside std::make_pair. *)
Definition pair_escape (t : tree) : (nat -> nat) * nat :=
  (sum_values t, 0).

Definition use_pair (p : (nat -> nat) * nat) : nat :=
  (fst p) (snd p).

(** Clobber stack after pair_escape returns. *)
Definition bug_pair_escape : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p1 := pair_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := pair_escape t2 in
  use_pair p1.

End PairClosureEscape.

Crane Extraction "pair_closure_escape" PairClosureEscape.
