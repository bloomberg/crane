From Crane Require Extraction.

(** A mutual inductive group whose cycle runs through a container.

    [tree] holds its children as a [list branch], and [branch] holds a [tree]
    back.  Neither struct can be emitted whole before the other: [Tree::leaf]
    takes a [List<Branch>] by value, which instantiates [List<Branch>] and so
    needs [Branch] complete, while [Branch::branch0] takes a [Tree] by value
    and needs [Tree] complete.  Crane emits each struct's layout and its
    methods together, one type at a time, and no order of the two satisfies
    both.

    At the top level the methods are emitted where they are written, so the
    cycle bites.  Inside a module the same group compiles, because a nested
    class's member bodies are only parsed once the enclosing class is
    complete -- which is why this test is not wrapped in a [Module].

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
