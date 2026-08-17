(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Ascii.


(** Enumerates the first [n] ASCII characters in descending order by code point. *)
Fixpoint asciiEnumFn (n : nat) : list ascii :=
        match n with
        | 0 => []
        | S m => (ascii_of_nat m) :: asciiEnumFn m
        end.

(** The complete list of all 256 ASCII characters. *)
Definition asciiEnum : list ascii := asciiEnumFn 256.

(** Every ASCII character appears in [asciiEnum]; proved by exhaustive bit-pattern case analysis. *)
Lemma ascii_finite : forall a : ascii, In a asciiEnum.
Proof.
  intros. destruct a.
  destruct b; destruct b0; destruct b1; destruct b2;
    destruct b3; destruct b4; destruct b5; destruct b6;
  repeat(try(left; reflexivity); right).
Qed.
