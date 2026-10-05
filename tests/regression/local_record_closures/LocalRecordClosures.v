From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

Module LocalRecordClosures.

(** A record of functions built and used in one place: each call through a
    field is that function's body at the call, and the record itself is gone.
    One that escapes keeps its representation. *)
Record ops := Ops { scale : nat -> nat; shift : nat -> nat }.

Definition use_local (n : nat) : nat :=
  let o := Ops (fun x => x * 2) (fun x => x + n) in
  shift o (scale o 3) + scale o n.

Definition make (n : nat) : ops := Ops (fun x => x * n) (fun x => x + n).

Definition two_records (a b : nat) : nat :=
  let p := Ops (fun x => x + a) (fun x => x * a) in
  let q := Ops (fun x => x + b) (fun x => x * b) in
  scale p 1 + shift q 2.

End LocalRecordClosures.

Crane Extraction "local_record_closures" LocalRecordClosures.
