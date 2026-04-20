From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ThisCaptureRecord.

(** A methodified function stores this-capturing closures in a
    Rocq record (not option/pair/fn_list). The record fields hold
    closures that reference tree_sum, which becomes this->tree_sum()
    in C++. After the temporary tree is destroyed, the closures'
    raw this pointer dangles.

    Different escape mechanism: record fields. *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l n r => tree_sum l + n + tree_sum r
  end.

(** A second inductive to prevent tree_callbacks from being
    methodified on callback_rec instead of tree. *)
Inductive tag : Type :=
  | MkTag : nat -> tag.

Record callback_rec := MkCR {
  cr_add : nat -> nat;
  cr_mul : nat -> nat
}.

(** Methodified on tree. The extra [flag] argument forces Crane to
    treat this as a multi-argument function (preventing eta-collapse).
    Returns a record whose fields are closures that capture [this]
    via [=, this]. *)
Definition tree_callbacks (t : tree) (flag : nat) : callback_rec :=
  match flag with
  | O => MkCR
           (fun x => x + tree_sum t)
           (fun x => x * tree_sum t)
  | S _ => MkCR
             (fun x => tree_sum t + x)
             (fun x => tree_sum t)
  end.

(** test1: flag=0, tree_sum=5.
    cr_add(10) = 10 + 5 = 15, cr_mul(3) = 3 * 5 = 15.
    Total = 30. *)
Definition test1 : nat :=
  let cb := tree_callbacks (Node Leaf 5 Leaf) 0 in
  cr_add cb 10 + cr_mul cb 3.

(** test2: With noise to clobber memory.
    flag=0, tree_sum = 60. cr_add(0) = 60, cr_mul(1) = 60.
    Total = 120. *)
Definition test2 : nat :=
  let cb := tree_callbacks
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) 0 in
  let noise := 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 in
  cr_add cb 0 + cr_mul cb 1.

(** test3: flag=1, tree_sum=100. cr_mul(7) = tree_sum = 100. *)
Definition test3 : nat :=
  cr_mul (tree_callbacks (Node Leaf 100 Leaf) 1) 7.

(** Dummy use of tag to keep it around for extraction. *)
Definition mk_tag (n : nat) : tag := MkTag n.

End ThisCaptureRecord.

Crane Extraction "this_capture_record" ThisCaptureRecord.
