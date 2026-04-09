From Stdlib Require Import Bool.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module RecordUseAfterMove.

Record box : Type := mkBox {
  payload : nat;
  enabled : bool
}.

Definition clone_box (b : box) : box :=
  mkBox (payload b) (enabled b).

Definition keep_box (b : box) : box :=
  b.

Definition use_box (b : box) : nat :=
  payload b.

Definition initial_box : box :=
  mkBox 41 true.

(** BUG: The same shared_ptr local [b] is moved into multiple call sites.
    After the first [std::move(b)], subsequent uses dereference a
    moved-from shared_ptr, causing a segfault. *)
Definition problematic : box :=
  let b := keep_box initial_box in
  let b1 := clone_box b in
  let b2 := clone_box b in
  if enabled (keep_box b)
  then if enabled b then b2 else b1
  else b1.

(** Simple case: same record used twice in let bindings. *)
Definition double_let : nat :=
  let b := initial_box in
  let x := payload b in
  let y := payload b in
  x + y.

(** Record passed to two different functions. *)
Definition two_consumers : nat :=
  let b := initial_box in
  let p := use_box b in
  let q := use_box b in
  p + q.

End RecordUseAfterMove.

Crane Extraction "record_use_after_move" RecordUseAfterMove.
