(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* SAFE APPROXIMATION: src/mlutil.ml line 221 — "this is just an approximation"

   The `generalizable` function marks non-MLapp expressions as generalizable in
   C++ mode. This is an approximation: in OCaml, MLcase/MLfix/etc. can be
   non-generalizable under certain conditions.

   Investigation: the approximation cannot be triggered by well-typed Rocq
   programs. Over-generalization would require using the same let-binding at
   two distinct concrete types in the same expression — Rocq's type checker
   prevents this. The incorrect marking is therefore unreachable from valid
   Rocq input, making this a latent issue rather than an observable bug.

   This test confirms the common case (let-bound function, let-bound MLapp)
   extracts correctly. It would only fail if a future Rocq version or an
   unusual Crane code path produced a let-binding used at two types. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TodoGeneralizableApprox.

  (* let-bound function (MLlam): correctly generalizable *)
  Definition apply_twice (f : nat -> nat) (x : nat) : nat :=
    let g := f in
    g (g x).

  (* let-bound application (MLapp): correctly non-generalizable *)
  Definition double_then_add (x : nat) : nat :=
    let y := x + x in
    y + 1.

  Definition test1 : nat := apply_twice (fun n => n + 1) 5.
  Definition test2 : nat := double_then_add 3.

End TodoGeneralizableApprox.

Crane Extraction "todo_generalizable_approx" TodoGeneralizableApprox.
