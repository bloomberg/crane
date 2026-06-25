From Stdlib Require Import List.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.
Import ListNotations.

Set Crane Loopify.

Module LoopifyFilterFnRef.

(** A binary tree with elements at nodes. *)
Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

(** Recursive filter: takes a predicate [f] and recurses on both subtrees.
    When loopified, [f] is stored in continuation frame structs.
    If [f] is passed as a function reference (e.g. a named function),
    the template parameter [F0] deduces to a reference type, and the
    generated frame struct field [F0 f] becomes ill-formed with std::move. *)
Fixpoint filter {A : Type} (f : A -> bool) (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l x r =>
      let l' := filter f l in
      let r' := filter f r in
      if f x then Node l' x r' else l'
  end.

(** A concrete predicate — will be passed as a function reference. *)
Definition is_positive (n : nat) : bool :=
  match n with
  | O => false
  | S _ => true
  end.

(** Entry point that calls filter with a named function. *)
Definition test_filter : tree nat :=
  filter is_positive (Node (Node Leaf 0 Leaf) 1 (Node Leaf 2 Leaf)).

End LoopifyFilterFnRef.

Crane Extraction "loopify_filter_fn_ref" LoopifyFilterFnRef.
