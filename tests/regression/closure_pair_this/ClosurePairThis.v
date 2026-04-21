From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosurePairThis.

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

Inductive wrapper : Type :=
  | Wrap : tree -> wrapper.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** BUG HYPOTHESIS: [get_fn_pair] returns two closures in a pair.
    When methodified, both closures capture the raw [this] pointer.
    The pair is custom-extracted as [std::make_pair], so the closures
    are evaluated and stored while [this] is still valid.
    But after [get_fn_pair] returns, the temporary tree may be
    destroyed — calling either closure is then use-after-free. *)

Definition get_fn_pair (t : tree) (flag : nat) : (nat -> nat) * (nat -> nat) :=
  match flag with
  | O => (fun x => x + tree_sum t, fun x => tree_sum t * x)
  | _ => (fun x => tree_sum t + x, fun x => x)
  end.

(** test1: flag=0 on tree with sum=7. fst closure adds, snd multiplies.
    (3 + 7) + (7 * 2) = 10 + 14 = 24. *)
Definition test1 : nat :=
  let p := get_fn_pair (Node Leaf 7 Leaf) 0 in
  fst p 3 + snd p 2.

(** test2: flag=1. fst closure adds sum, snd is identity.
    (7 + 4) + 5 = 11 + 5 = 16. *)
Definition test2 : nat :=
  let p := get_fn_pair (Node Leaf 7 Leaf) 1 in
  fst p 4 + snd p 5.

(** test3: Use both closures after allocating another tree to increase
    memory pressure on the freed region. *)
Definition test3 : nat :=
  let p := get_fn_pair (Node (Node Leaf 3 Leaf) 5 (Node Leaf 2 Leaf)) 0 in
  let noise := tree_sum (Node Leaf 999 Leaf) in
  let a := fst p noise in
  let b := snd p 1 in
  a + b.

(** test3 expected: tree sum = 3+5+2 = 10. noise = 999.
    fst p noise = 999 + 10 = 1009. snd p 1 = 10 * 1 = 10.
    Total: 1009 + 10 = 1019. *)

End ClosurePairThis.

Crane Extraction "closure_pair_this" ClosurePairThis.
