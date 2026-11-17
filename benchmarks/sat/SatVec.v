(** Mutable, reference-semantics vectors as an ITree effect.

    The same Rocq program is extracted twice: by Crane, where the tree is
    erased and each event is a direct call on [satbench::vec], and by stock
    OCaml extraction, where the tree is built and [vec_run.ml] interprets the
    events over OCaml arrays. *)
From Stdlib Require Import List.
From Crane Require Import Monads.ITree.

(** A vector is a location in the heap the events act on.  Both extractions
    replace [vec] wholesale, so this only matters to the proofs, which need
    handles they can compare and allocate.  It is a record rather than a
    definition so that [vec A] stays a type constructor of its own: OCaml
    extraction would otherwise unfold [vec int] and [vec Obj.t] to the same
    [int] and leave out the [Obj.magic] between them. *)
Definition loc := nat.
Record vec (A : Type) : Type := mk_vec { vloc : loc }.
Arguments mk_vec {A}.
Arguments vloc {A}.

Inductive vecE : Type -> Type :=
| VMake : forall {A}, nat -> A -> vecE (vec A)
| VGet : forall {A}, vec A -> nat -> vecE A
| VSet : forall {A}, vec A -> nat -> A -> vecE unit
| VLen : forall {A}, vec A -> vecE nat
| VPush : forall {A}, vec A -> A -> vecE unit
| VShrink : forall {A}, vec A -> nat -> vecE unit
(** Give up: the loop numbered [site] ran out of fuel.  No answer ever comes back, so a run
    that aborts has no result to be wrong about. *)
| VAbort : forall {A}, nat -> vecE A.

Section Ops.
Context {E : Type -> Type} `{vecE -< E}.
Definition vmake {A} (n : nat) (x : A) : itree E (vec A) := embed (VMake n x).
Definition vget {A} (v : vec A) (i : nat) : itree E A := embed (VGet v i).
Definition vset {A} (v : vec A) (i : nat) (x : A) : itree E unit := embed (VSet v i x).
Definition vlen {A} (v : vec A) : itree E nat := embed (VLen v).
Definition vpush {A} (v : vec A) (x : A) : itree E unit := embed (VPush v x).
Definition vshrink {A} (v : vec A) (n : nat) : itree E unit := embed (VShrink v n).
Definition vabort {A} (site : nat) : itree E A := embed (VAbort site).
End Ops.
