From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module MutualValueDeepCopy.

(** Direct self-recursive value ADTs now get iterative clone/destruct paths.
    This test uses mutual recursion instead: [a] owns [b], and [b] owns [a].
    Crane currently generates recursive [a::clone] and [b::clone] methods that
    call each other through [unique_ptr] children.  Copying a deep alternating
    value with [dup_a] therefore overflows the C++ stack before the copied value
    can be used. *)

Inductive a : Type :=
| AEnd : a
| ANode : bool -> b -> a
with b : Type :=
| BNode : a -> b.

Fixpoint reaches_end_a (x : a) : bool :=
  match x with
  | AEnd => true
  | ANode _ y => reaches_end_b y
  end
with reaches_end_b (y : b) : bool :=
  match y with
  | BNode x => reaches_end_a x
  end.

Definition dup_a (x : a) : a * a := (x, x).

Definition copied_reaches_end (x : a) : bool :=
  let '(x1, x2) := dup_a x in
  andb (reaches_end_a x1) (reaches_end_a x2).

End MutualValueDeepCopy.

Crane Extraction "mutual_value_deep_copy" MutualValueDeepCopy.
