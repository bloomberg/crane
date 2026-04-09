From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ListClosureEscape.

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

(** A simple list of closures. *)
Inductive fn_list : Type :=
| FNil : fn_list
| FCons : (nat -> nat) -> fn_list -> fn_list.

(** BUG: partial applications stored in a custom list via FCons.
    Each lambda for (sum_values t_i) captures t_i by [&].
    When build_fns returns, t1 and t2 are destroyed. *)
Definition build_fns (t1 t2 : tree) : fn_list :=
  FCons (sum_values t1) (FCons (sum_values t2) FNil).

Definition apply_first (fns : fn_list) (x : nat) : nat :=
  match fns with
  | FNil => x
  | FCons f _ => f x
  end.

Definition bug_list_clobber : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let fns := build_fns t1 t2 in
  apply_first fns 0.

End ListClosureEscape.

Crane Extraction "list_closure_escape" ListClosureEscape.
