(** Mutable, reference-semantics vectors as an ITree effect.

    The same Rocq program is extracted twice: by Crane, where the tree is
    erased and each event is a direct call on [satbench::vec], and by stock
    OCaml extraction, where the tree is built and [itree_run.ml] interprets
    the events over OCaml arrays. *)
From Stdlib Require Import List.
From Crane Require Import Monads.ITree.

(** A heap location: what a [vec] handle denotes in the proofs. *)
Definition loc := nat.
(** A vector is a location in the heap the events act on.  Both extractions
    replace [vec] wholesale, so this only matters to the proofs, which need
    handles they can compare and allocate.  It is a record rather than a
    definition so that [vec A] stays a type constructor of its own: OCaml
    extraction would otherwise unfold [vec int] and [vec Obj.t] to the same
    [int] and leave out the [Obj.magic] between them. *)
Record vec (A : Type) : Type := mk_vec { vloc : loc }.
Arguments mk_vec {A}.
Arguments vloc {A}.

(** The vector effect; [VecSem.step] says what each event does. *)
Inductive vecE : Type -> Type :=
(** A fresh vector of [n] copies of [x]. *)
| VMake : forall {A}, nat -> A -> vecE (vec A)
(** The element at an index, which must be in bounds. *)
| VGet : forall {A}, vec A -> nat -> vecE A
(** Overwrite the element at an index, which must be in bounds. *)
| VSet : forall {A}, vec A -> nat -> A -> vecE unit
(** The current length. *)
| VLen : forall {A}, vec A -> vecE nat
(** Append one element; vectors grow, so the solver can add learnt clauses. *)
| VPush : forall {A}, vec A -> A -> vecE unit
(** Cut to the first [n] elements, [n] at most the length. *)
| VShrink : forall {A}, vec A -> nat -> vecE unit
(** Give up: the loop numbered [site] ran out of fuel.  No answer ever comes back, so a run
    that aborts has no result to be wrong about. *)
| VAbort : forall {A}, nat -> vecE A.

(** Smart constructors, one event each, in any effect containing [vecE].
    Crane and the hand-erased OCaml control map these to direct calls. *)
Section Ops.
Context {E : Type -> Type} `{vecE -< E}.
(** Allocate a vector of [n] copies of [x]. *)
Definition vmake {A} (n : nat) (x : A) : itree E (vec A) := embed (VMake n x).
(** Read element [i]. *)
Definition vget {A} (v : vec A) (i : nat) : itree E A := embed (VGet v i).
(** Write element [i]. *)
Definition vset {A} (v : vec A) (i : nat) (x : A) : itree E unit := embed (VSet v i x).
(** The length of [v]. *)
Definition vlen {A} (v : vec A) : itree E nat := embed (VLen v).
(** Append [x] to [v]. *)
Definition vpush {A} (v : vec A) (x : A) : itree E unit := embed (VPush v x).
(** Truncate [v] to length [n]. *)
Definition vshrink {A} (v : vec A) (n : nat) : itree E unit := embed (VShrink v n).
(** Give up at loop [site]: where every fuel-bounded loop of the solver ends
    when its fuel does. *)
Definition vabort {A} (site : nat) : itree E A := embed (VAbort site).
End Ops.
