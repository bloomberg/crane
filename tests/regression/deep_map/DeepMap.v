From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module DeepMap.

Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A}.

(** Build a maximally-unbalanced tree (right spine = linked list).
    Tail-recursive via accumulator, should be loopified. *)
Fixpoint build_right (n : nat) (acc : tree nat) : tree nat :=
  match n with
  | O => acc
  | S n' => build_right n' (node leaf n acc)
  end.

(** Recursive tree map — visits every node. *)
Fixpoint tmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | leaf => leaf
  | node l x r => node (tmap f l) (f x) (tmap f r)
  end.

Definition map_inc (t : tree nat) : tree nat := tmap (fun x => x + 1) t.

(** Get root value. *)
Definition root_or_zero (t : tree nat) : nat :=
  match t with
  | leaf => 0
  | node _ x _ => x
  end.

End DeepMap.

Crane Extraction "deep_map" DeepMap.
