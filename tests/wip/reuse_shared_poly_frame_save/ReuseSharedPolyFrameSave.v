From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Reuse.
Set Crane SharedVariant.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Reuse and SharedVariant, a polymorphic non-tail local fixpoint
    building a list of lists fails the ownership check under CRANE_CHECK_IR=1:
    "frame save: a let a frame machine resumes at is generated saving its
    frame otherwise than it was before". *)
Module ReuseSharedPolyFrameSave.

Definition f {A : Type} (a : A) : list (list A) :=
  let fix go (l : list (list A)) (acc : list (list A)) {struct l} : list (list A) :=
    match l with [] => acc | e :: rest => let rv := go rest acc in e :: rv end in
  go [[]] [[]].

Definition t : nat := List.length (f 1).

End ReuseSharedPolyFrameSave.

Crane Extraction "reuse_shared_poly_frame_save" ReuseSharedPolyFrameSave.
