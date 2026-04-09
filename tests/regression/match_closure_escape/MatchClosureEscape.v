From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module MatchClosureEscape.

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

(** A box for closures, forces the closure to be stored on the heap. *)
Inductive fn_box : Type :=
| Box : (nat -> nat) -> fn_box.

Definition apply_box (b : fn_box) (x : nat) : nat :=
  match b with
  | Box f => f x
  end.

(** BUG TRIGGER: match_arm_box
    The partial application [sum_values l] inside a match arm creates a
    [&] lambda capturing the match-bound variable _args (from std::visit).
    This lambda is stored in a Box constructor argument.
    return_captures_by_value does NOT handle lambdas inside constructor args.
    When the visit lambda returns, _args goes out of scope, and the Box
    holds a dangling reference to a destroyed shared_ptr. *)
Definition match_arm_box (t : tree) : fn_box :=
  match t with
  | Leaf => Box (fun x => x)
  | Node l v r => Box (sum_values l)
  end.

(** Use a top-level definition to get a shared_ptr (not unique_ptr). *)
Definition test_tree : tree :=
  Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf).

Definition bug_match_box : nat :=
  apply_box (match_arm_box test_tree) 99.

End MatchClosureEscape.

Crane Extraction "match_closure_escape" MatchClosureEscape.
