From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

Module LastUsePlaces.

(** A local's last reads become moves -- all of it, or each of its members
    when every read is of a different one -- and never a read the C++ may
    evaluate again. *)
Axiom big : Type.
Axiom mk_big : nat -> big.
Axiom big_val : big -> nat.
Axiom twice_val : big -> nat.
Crane Extract Inlined Constant big => "Big" From "big_support.h".
Crane Extract Inlined Constant mk_big => "Big(%a0)".
Crane Extract Inlined Constant big_val => "%a0.v".
Crane Extract Inlined Constant twice_val => "sum_twice(%a0, %a0)".

Definition split (n : nat) : big * big := (mk_big n, mk_big (S n)).

(** Each member of the dead local [q] read once: both move. *)
Definition swap_fields (n : nat) : big * big :=
  let q := split n in (snd q, fst q).

(** [b] read twice, whole: neither read may move. *)
Definition twice (n : nat) : big * big := let b := mk_big n in (b, b).

(** A member of [q] and [q] itself: neither may move. *)
Definition both (n : nat) : big * (big * big) := let q := split n in (fst q, q).

(** A template that splices its argument twice. *)
Definition dup (n : nat) : nat := let b := mk_big n in twice_val b.

End LastUsePlaces.

Crane Extraction "last_use_places" LastUsePlaces.
