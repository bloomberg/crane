(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: exercises interoperability between arena-mode types (Part 3's
   explicit-arena-parameter design) and ordinary shared_ptr-mode types:
     (a) a non-arena record holding an arena-mode value as a field, and
     (b) the arena-mode type itself parameterized over a non-arena,
         shared_ptr-mode recursive payload (to confirm its refcounting is
         untouched by the arena opt-in, which only applies to the
         [tree] type itself, not its type parameter). *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Interop.

(* Arena-mode recursive tree, parameterized over an arbitrary payload type. *)
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} t1 x t2.

Fixpoint count {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + count l + count r
  end.

(* An ordinary (non-arena, shared_ptr-mode) recursive payload type: a plain
   linked list of nats.  Used as tree's type parameter in (b) below to
   confirm shared_ptr refcounting on the payload is unaffected by the
   arena opt-in, which is scoped to [tree] alone. *)
Inductive nlist : Type :=
| nnil : nlist
| ncons : nat -> nlist -> nlist.

Fixpoint nlist_len (l : nlist) : nat :=
  match l with
  | nnil => 0
  | ncons _ rest => 1 + nlist_len rest
  end.

(* (a) A non-arena (ordinary shared_ptr-mode) record with an arena-mode
   value as a field.  Since [tree nat]'s own struct is a small value type
   (a variant holding raw pointers into its owning arena, per the Option 1
   design), an ordinary record can hold it by value: the record's
   compiler-generated copy/move/destroy just delegate to [tree]'s own
   copy/move/destroy, which is already deep-copy-safe (verified by
   arena_tree's copy-constructor test). No special handling should be
   needed here — this test exists to confirm that expectation holds for
   the *generated* code too, not just hand-rolled C++. *)
Record wrapper : Type := mkwrapper {
  w_id : nat;
  w_tree : tree nat;
}.

Definition wrapper_size (w : wrapper) : nat := count (w_tree w).

End Interop.

Require Crane.Extraction.
Crane Arena Interop.tree.
Crane Extraction "arena_interop" Interop.
