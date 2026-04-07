From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module OptionClosureEscape.

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

(** BUG: pair_escape stores a [&] lambda in a pair.
    The lambda captures parameter t by reference.
    When pair_escape returns, t is destroyed → dangling. *)
Definition pair_escape (t : tree) : (nat -> nat) * nat :=
  (sum_values t, 42).

(** Call pair_escape, then call it again to clobber the stack,
    then use the first result's closure. *)
Definition bug_pair_clobber : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p1 := pair_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let p2 := pair_escape t2 in
  let _ := snd p2 in
  (fst p1) 0.

(** BUG: match_pair — [&] captures _args from visit scope. *)
Definition match_pair (t : tree) : (nat -> nat) * nat :=
  match t with
  | Leaf => (fun x => x, 0)
  | Node l v r => (sum_values l, v)
  end.

Definition bug_match_pair_clobber : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p1 := match_pair t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let p2 := match_pair t2 in
  let _ := snd p2 in
  (fst p1) 0.

End OptionClosureEscape.

Crane Extraction "option_closure_escape" OptionClosureEscape.
