(** Global arrays: every array operation of [Global], extracted to direct
    accesses on a [crane::array_storage]. *)
From Stdlib Require Import Arith.PeanoNat List PrimString.
From ITree Require Import ITree Events.Exception.
From Crane Require Monads.Global.
From Crane Require Import
  Extraction
  Mapping.NatInt
  Mapping.Std
  Monads.Error
  Monads.Indices
  Monads.ITree
.
Import ListNotations.
Import Monads.
Local Open Scope monad_scope.

Module GlobalArrays.

(** Every index holds [nat]s.  A notation, so that [V 0] reduces to [nat]
    where Crane reads the types. *)
Notation V := (fun _ : nat => nat).

(** The program's effects: global state at [nat] locations, and errors.  A
    notation, not a definition: a C++ alias for it would have to spell the
    erased [RefClass] instance argument of [Global.Event]. *)
Notation E0 := (Global.Event nat V +' exceptE Err).

(** A global array of [nat]s, made at index [0]. *)
Definition nat_array : Type := Global.array nat (V 0).

(** Write [i * i] into each of the first [k] cells, last first. *)
Fixpoint fill_squares (arr : nat_array) (k : nat) : itree E0 unit :=
  match k with
  | O => Ret tt
  | S k' => Global.write_array arr k' (k' * k');; fill_squares arr k'
  end.


(** The squares below [n], built in a fresh array. *)
Definition squares (n : nat) : itree E0 (list nat) :=
  arr <- Global.new_array 0 n 0;;
  fill_squares arr n;;
  Global.array_to_list arr.

(** The sum of the first [k] cells of [arr], read one at a time. *)
Fixpoint sum_cells (arr : nat_array) (k : nat) (acc : nat) : itree E0 nat :=
  match k with
  | O => Ret acc
  | S k' => x <- Global.read_array arr k';; sum_cells arr k' (acc + x)
  end.

(** The sum of [xs], through an array made from it. *)
Definition sum_list (xs : list nat) : itree E0 nat :=
  arr <- Global.array_of_list 0 xs;;
  sum_cells arr (List.length xs) 0.

(** [xs] with its first and last elements exchanged in an array. *)
Definition swap_ends (xs : list nat) : itree E0 (list nat) :=
  arr <- Global.array_of_list 0 xs;;
  Global.swap_array arr 0 (List.length xs - 1);;
  Global.array_to_list arr.

(** A written cell reads back the new value, its neighbours the default. *)
Definition write_then_read : itree E0 (nat * nat) :=
  arr <- Global.new_array 0 3 7;;
  Global.write_array arr 1 42;;
  a <- Global.read_array arr 1;;
  b <- Global.read_array arr 2;;
  Ret (a, b).

(** Arrays and references share the store: a reference made after an array
    reads back its own value. *)
Definition array_then_ref : itree E0 nat :=
  arr <- Global.new_array 0 2 1;;
  r <- Global.new_ref 0 5;;
  Global.write_array arr 0 9;;
  x <- Global.read_ref r;;
  y <- Global.read_array arr 0;;
  Ret (x + y).

End GlobalArrays.

Crane Extraction "global_arrays" GlobalArrays.
