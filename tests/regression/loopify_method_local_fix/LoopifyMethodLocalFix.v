(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A local fixpoint in a function generated as a method of its inductive.

    Loopify lowers the local fixpoints in the body of every function it
    transforms, after the function's own loop, but it lowered a method's
    own recursion only: [drain], a method of [tree], counted down through a
    lambda calling itself, one C++ stack frame per step. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module LoopifyMethodLocalFix.

Module Tree.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree.

Fixpoint drain (t : tree) (n : nat) : nat :=
  match t with
  | Leaf =>
    let fix go (k acc : nat) : nat :=
      match k with O => acc | S k' => go k' (S acc) end in
    go n 0
  | Node l m => drain l (n + m)
  end.

End Tree.

End LoopifyMethodLocalFix.

Crane Extraction "loopify_method_local_fix" LoopifyMethodLocalFix.
