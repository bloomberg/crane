From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module OptionSomeEscape.

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

(** BUG: Partial application stored in Some (std::make_optional).
    The [&] lambda captures parameter t by reference.
    return_captures_by_value doesn't handle lambdas inside
    std::make_optional. When the function returns, t is destroyed. *)
Definition option_escape (t : tree) : option (nat -> nat) :=
  Some (sum_values t).

Definition apply_option (o : option (nat -> nat)) (x : nat) : nat :=
  match o with
  | None => x
  | Some f => f x
  end.

(** Clobber stack, then use the closure from the option. *)
Definition bug_option_some : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let o1 := option_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := option_escape t2 in
  apply_option o1 0.

End OptionSomeEscape.

Crane Extraction "option_some_escape" OptionSomeEscape.
