From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module LetClosureEscape.

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

Inductive fn_box : Type :=
| Box : (nat -> nat) -> fn_box.

Definition apply_box (b : fn_box) (x : nat) : nat :=
  match b with
  | Box f => f x
  end.

(** BUG: let-bound partial application returned through a Box.
    f := sum_values t creates a [&] lambda bound to a variable.
    Box f stores the variable (not a direct lambda) in a constructor.
    When let_escape returns, t is destroyed → dangling reference in Box. *)
Definition let_escape (t : tree) : fn_box :=
  let f := sum_values t in
  let _ := f 0 in
  Box f.

(** Clobber stack after let_escape returns, then use the closure. *)
Definition bug_let_clobber : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b1 := let_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := let_escape t2 in
  apply_box b1 0.

End LetClosureEscape.

Crane Extraction "let_closure_escape" LetClosureEscape.
