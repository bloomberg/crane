(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Monads.Thread] maps a [thread] to [std::thread], whose rules
    a Rocq program is not bound by.
    - A thread spawned and never joined: destroying a joinable
      [std::thread] calls [std::terminate].
    - A thread joined twice: the second [join] throws [std::system_error]
      ("thread::join failed: Invalid argument").
    - Threads kept in a [list] are [const] elements, and
      [std::thread::join] is not [const]: "'this' argument to member
      function 'join' has type 'const std::thread'".
    A handle shared by its copies, joining at most once (and on its last
    release), has the semantics the Rocq type has. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO Monads.Thread.

Module ThreadHandleSemantics.

Open Scope itree_scope.

Definition work (n : nat) : itree concE unit := Ret tt.

Definition never_joined (n : nat) : itree concE nat := t <- spawn work n ;; Ret n.

Definition joined_twice (n : nat) : itree concE nat := t <- spawn work n ;; join t ;; join t ;; Ret n.

Fixpoint spawn_all (l : list nat) : itree concE (list thread) :=
  match l with [] => Ret [] | x :: t => h <- spawn work x ;; hs <- spawn_all t ;; Ret (h :: hs) end.

Fixpoint join_all (l : list thread) : itree concE unit :=
  match l with [] => Ret tt | h :: t => join h ;; join_all t end.

Definition r1 : nat := runConc (never_joined 3).
Definition r2 : nat := runConc (joined_twice 4).
Definition r3 : nat := runConc (hs <- spawn_all [1; 2; 3] ;; join_all hs ;; Ret 7).

End ThreadHandleSemantics.

Crane Extraction "thread_handle_semantics" ThreadHandleSemantics.
