(** A local fixpoint polymorphic in a type of its own is lifted out of its
    definition as a helper, and a helper whose recursion is not a tail loop
    becomes a machine with a stack of frames.  Its frames may hold a
    parameter by pointer wherever every value passed for it lies in what the
    caller passed, as a function's do.

    [zigzag]'s helper walks its first tree and passes its second either
    itself or a subtree of the first: the second is not always passed a part
    of what was passed for it, but always a part of what was passed for one
    of them, so both can be held by pointer. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Set Crane Loopify.

Module LiftedHelperFramePointer.

  Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

  Arguments Leaf {A}.
  Arguments Node {A} _ _ _.

  Definition depth_at {B} (b : tree B) : nat :=
    match b with Leaf => 0 | Node _ _ _ => 1 end.

  (** Each leaf of [a] counts 1 where the tree passed beside it is a node.
      Used at two types, the fixpoint stays polymorphic, and is lifted. *)
  Definition zigzag (t u : tree nat) (s w : tree bool) : nat :=
    let fix go {B} (a b : tree B) : nat :=
      match a with
      | Leaf => depth_at b
      | Node l _ r => go l b + go r l
      end
    in go t u + 1000 * go s w.

  (** The same recursion at the top level, not lifted: the driver's
      reference. *)
  Fixpoint go_ref {B} (a b : tree B) : nat :=
    match a with
    | Leaf => depth_at b
    | Node l _ r => go_ref l b + go_ref r l
    end.

  Fixpoint full_bool (n : nat) : tree bool :=
    match n with
    | O => Leaf
    | S k => Node (full_bool k) (Nat.even k) (full_bool k)
    end.

  Fixpoint spine (n : nat) : tree nat :=
    match n with
    | O => Leaf
    | S k => Node Leaf k (spine k)
    end.

  Fixpoint full (n : nat) : tree nat :=
    match n with
    | O => Leaf
    | S k => Node (full k) k (full k)
    end.

End LiftedHelperFramePointer.

Crane Extraction "lifted_helper_frame_pointer" LiftedHelperFramePointer.
