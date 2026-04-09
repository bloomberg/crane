From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module MatchCtorClosure.

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

(** BUG HYPOTHESIS: Match arm stores a partial application (closure)
    in a constructor. The lambda captures a PATTERN VARIABLE (_args.d_a0)
    by [&] reference. When the visit lambda returns, _args is destroyed
    but the fn_box retains the closure with a dangling reference. *)
Definition match_and_box (t : tree) : fn_box :=
  match t with
  | Leaf => Box (fun x => x)
  | Node l v r => Box (sum_values l)
  end.

(** Clobber stack, then use the closure from the box. *)
Definition bug_match_ctor : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := match_and_box t in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := match_and_box t2 in
  apply_box b 5.

End MatchCtorClosure.

Crane Extraction "match_ctor_closure" MatchCtorClosure.
