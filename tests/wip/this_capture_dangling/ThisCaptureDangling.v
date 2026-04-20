From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ThisCaptureDangling.

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

Inductive wrapper : Type :=
  | Wrap : tree -> wrapper.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** BUG HYPOTHESIS: When [get_fn] is methodified (tree is the only inductive),
    the first argument [t] becomes the raw [this] pointer.

    The return type is [option (nat -> nat)] — one branch returns [None],
    the other returns [Some (fun x => x + tree_sum t)]. The [option] wrapper
    prevents lambda flattening, so the inner lambda IS a genuine C++ lambda.

    The lambda captures [this] via [=, this]. Since the return type
    does NOT contain [shared_ptr<tree>], [replace_return_this_stmt] is NOT
    applied — [this] stays as a raw pointer. If the closure outlives the
    tree's [shared_ptr], we have use-after-free.

    Note: [option] is custom-extracted to [std::optional]. *)

Definition get_fn (t : tree) : option (nat -> nat) :=
  match tree_sum t with
  | O => None
  | _ => Some (fun x => x + tree_sum t)
  end.

(** test1: Call [get_fn] on a temporary tree with sum=42.
    The tree shared_ptr is released after [get_fn] returns.
    Unwrapping the option and calling the closure dereferences
    the dangling [this].
    Expected: match result is Some f, then f 10 = 10 + 42 = 52. *)
Definition test1 : nat :=
  match get_fn (Node Leaf 42 Leaf) with
  | Some f => f 10
  | None => 999
  end.

(** test2: Same pattern with a larger tree (sum = 42).
    Expected: 5 + 42 = 47. *)
Definition test2 : nat :=
  match get_fn (Node (Node Leaf 10 Leaf) 20 (Node Leaf 12 Leaf)) with
  | Some f => f 5
  | None => 999
  end.

(** test3: Allocate another tree between getting the closure and calling it.
    This increases memory pressure on the freed region.
    Expected: f noise = noise + 100 where noise = 1+2+3 = 6. So 106. *)
Definition test3 : nat :=
  let opt := get_fn (Node Leaf 100 Leaf) in
  let noise := tree_sum (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) in
  match opt with
  | Some f => f noise
  | None => 999
  end.

End ThisCaptureDangling.

Crane Extraction "this_capture_dangling" ThisCaptureDangling.
