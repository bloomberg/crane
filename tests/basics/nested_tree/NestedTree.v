(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module NestedTree.

(* Nested tree type: each level contains a more complex product of values *)
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : A -> tree (A * A) -> tree A.

Arguments leaf {A}.
Arguments node {A} a t.

(* Level 0:          1         : nat
                   / \
   Level 1:      (2, 3)        :: nat * nat
               /        \
   Level 2:  ((4, 5), (6, 7))  :: (nat * nat) * (nat * nat)
*)
Definition example1 : tree nat :=
  node 1 (node (2, 3) (node ((4, 5), (6, 7)) leaf)).

Definition lift {A B : Type} (f : A -> list B) (p : A * A) : list B :=
  let (x, y) := p in f x ++ f y.

Definition flatten_tree {A : Type} (t : tree A) : list (list A) :=
  let fix go {A B : Type} (f : A -> list B) (t : tree A) : list (list B) :=
    match t with
    | leaf => []
    | node a t => f a :: go (lift f) t
    end
  in go (fun x => [x]) t.

End NestedTree.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Crane Extraction TestCompile "nested_tree" NestedTree.
