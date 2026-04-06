From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module ClosureCaptureMatch.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** Return a closure from a match branch.
    The closure captures shared_ptr fields (left, right subtrees).
    If capture is by-reference instead of by-value, the closure
    would have dangling references after the match lambda returns. *)
Definition make_inserter (t : tree) : nat -> tree :=
  match t with
  | Leaf => fun v => Node Leaf v Leaf
  | Node l _ r => fun v => Node l v r
  end.

(** Nested match returning a closure.
    The closure captures fields from BOTH match levels. *)
Definition deep_capture (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun x => x
  | Node l v r =>
    match l with
    | Leaf => fun x => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => fun x => lv + x
      | Node _ rv _ => fun x => lv + rv + v + x
      end
    end
  end.

(** Store a closure in a data structure (not directly returned). *)
Inductive fn_box : Type :=
| Box : (nat -> nat) -> fn_box.

Definition box_from_match (t : tree) : fn_box :=
  match t with
  | Leaf => Box (fun x => x)
  | Node _ v _ => Box (fun x => v + x)
  end.

Definition unbox (b : fn_box) (x : nat) : nat :=
  match b with
  | Box f => f x
  end.

(** Closure that captures a shared_ptr and is called AFTER
    the original data structure is dropped. *)
Definition capture_and_drop (t : tree) : nat :=
  let f := make_inserter t in
  (* t can be dropped here if it's the last use *)
  match f 42 with
  | Leaf => 0
  | Node _ v _ => v
  end.

(** Build a tree, extract closures, drop the tree, use closures. *)
Definition test_capture : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := deep_capture t in
  let b := box_from_match t in
  (* At this point, closures f and b hold copies of tree data.
     If they captured by reference, the data would be dangling. *)
  f 5 + unbox b 7.

End ClosureCaptureMatch.

Crane Extraction "closure_capture_match" ClosureCaptureMatch.
