From Crane Require Extraction.

(** A mutual inductive group whose cycle runs through a container.

    [tree] holds its children as a [list branch], and [branch] holds a [tree]
    back.  Neither struct can be written whole before the other: [Tree::leaf]
    takes a [List<Branch>] by value, which instantiates [List<Branch>] and so
    needs [Branch] complete, while [Branch::branch0] takes a [Tree] by value
    and needs [Tree] complete.  The members that cross the cycle are written
    after the whole group, which is the order that exists.

    The group is at the top level on purpose: inside a module a nested class's
    member bodies are only compiled once the enclosing class is complete, so
    the cycle would not bite.

    Reported as bug #130. *)

Inductive tree : Set :=
| Leaf : list branch -> tree
with branch : Set :=
| Branch : nat -> tree -> branch.

Fixpoint tree_size (t : tree) : nat :=
  match t with
  | Leaf bs =>
      S ((fix branches_size (l : list branch) : nat :=
            match l with
            | nil => 0
            | cons b rest => branch_size b + branches_size rest
            end) bs)
  end
with branch_size (b : branch) : nat :=
  match b with
  | Branch _ t => S (tree_size t)
  end.

Crane Extraction "mutual_list_cycle" tree branch tree_size branch_size.
