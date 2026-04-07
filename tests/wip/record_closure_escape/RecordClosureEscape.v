From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module RecordClosureEscape.

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

(** A record holding a closure and a value. Records are single-constructor
    inductives and get special treatment in Crane's translation. *)
Record fn_record := mk_fn_record {
  fn_field : nat -> nat;
  val_field : nat
}.

(** BUG: Partial application stored in a record field.
    The record constructor mk_fn_record stores the [&] lambda.
    return_captures_by_value doesn't handle lambdas inside
    record constructor arguments. *)
Definition record_escape (t : tree) : fn_record :=
  mk_fn_record (sum_values t) 42.

Definition use_record (r : fn_record) : nat :=
  fn_field r (val_field r).

(** Clobber stack after record_escape returns. *)
Definition bug_record_escape : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let r1 := record_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := record_escape t2 in
  use_record r1.

End RecordClosureEscape.

Crane Extraction "record_closure_escape" RecordClosureEscape.
