From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    Under Loopify, a mutual fixpoint whose recursive branch nests a non-tail local fixpoint (its base read by an inner local fixpoint) under [mod] fails the frame-plan check under CRANE_CHECK_IR=1: "a frame keeps a binder whose local was declared at no type".

    [go16]'s machine kept [n12], a capture of the enclosing function, which
    the rest reads through [go22]'s call: the inner loop dropped the
    argument that named it, so the machine's body no longer did, and only
    what the body names counted as bound outside the machine.  Its handler
    even assigned the frame's copy back to the captured [n12].  A local
    fixpoint's captures now count as invariant whether or not the body
    names them. *)
Module LoopifyMutualFrameUntypedBinder.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => (tree_obs l * 7 + v + tree_obs r * 3) mod 10007
  end.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_list {A : Type} : Mon (list A) := { munit := []; mop := @app A }.

Fixpoint h1a (n3 : nat) (a1 : ((list string) * bool)) : (option (sum nat string)) :=
  (@None (sum nat string))
with h1b (n12 : nat) (a2 : (list (option nat))) : nat :=
  match n12 with O => ((match n12 with O => 260%nat | S m13 => (tree_obs (Node Leaf 272%nat Leaf)) end) - (tree_obs (match n12 with O => (Node Leaf 12%nat Leaf) | S m14 => (Node Leaf 11%nat Leaf) end)))%nat | S m15 => ((let fix go16 (l17 : (list bool)) (acc18 : nat) {struct l17} : nat := match l17 with [] => (tree_obs (Node Leaf 11%nat Leaf)) | e19 :: rest20 => let rv21 := go16 rest20 acc18 in (let fix go22 (l23 : (list string)) (acc24 : nat) {struct l23} : nat := match l23 with [] => rv21 | e25 :: rest26 => go22 rest26 n12 end in go22 [""%string; "hello"%string] 11%nat) end in go16 (mop [true; true; false] [false; true]) (if true then n12 else 88%nat)) mod (if (let x27 := (Some 11%nat) in false) then (if true then 7%nat else m15) else (match n12 with O => m15 | S m28 => m28 end)))%nat
  end.
End LoopifyMutualFrameUntypedBinder.

Crane Extraction "loopify_mutual_frame_untyped_binder" LoopifyMutualFrameUntypedBinder.
