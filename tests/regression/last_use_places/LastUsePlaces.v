From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Mapping.Std Mapping.NatInt.
From Crane Require Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Module LastUsePlaces.

(** A local's last reads become moves -- all of it, or each of its members
    when every read is of a different one -- and never a read the C++ may
    evaluate again. *)
Axiom big : Type.
Axiom mk_big : nat -> big.
Axiom big_val : big -> nat.
Axiom twice_val : big -> nat.
#[global] Instance big_mapping : TypeMapping big :=
  value_type ["big_support.h"] (Name "Big") UnknownCopy.
#[global] Instance mk_big_mapping : OperationMapping (Ref (@mk_big)) :=
  pure_cpp [] ["x0"]
    (Structured (Call "Big" [] [Arg "x0"])).
#[global] Instance big_val_mapping : OperationMapping (Ref (@big_val)) :=
  pure_cpp [] ["x0"]
    (Structured (Member (Arg "x0") "v")).
#[global] Instance twice_val_mapping : OperationMapping (Ref (@twice_val)) :=
  pure_cpp [] ["x0"]
    (Structured (Call "sum_twice" [] [Arg "x0"; Arg "x0"])).

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
