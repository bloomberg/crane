
From Crane Require Extraction.
From Crane.Mapping Require GoStd.

(** A simple inductive type *)
Inductive color := Red | Green | Blue.

(** A simple function *)
Definition is_red (c : color) : bool :=
  match c with
  | Red => true
  | _ => false
  end.

(** A recursive function *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** A parameterized inductive *)
Inductive tree (A : Type) :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {A}.
Arguments Node {A}.

(** A function on trees *)
Fixpoint size {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf => O
  | Node l _ r => S (add (size l) (size r))
  end.

Crane Recursive Extraction color is_red add tree size.
