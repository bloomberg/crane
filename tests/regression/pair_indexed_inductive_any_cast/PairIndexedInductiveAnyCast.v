From Crane Require Extraction.
From Crane Require Import Mapping.Std.

(** Type-indexed inductive where the constructor field is a pair.
    The type index A is erased to [std::any]; accessing [fst]/[snd] of
    the pair field must emit [std::any_cast<A>] in generated C++. *)
Inductive pair_wrap : Type -> Type :=
  | mk_pair_wrap : forall A : Type, (A * nat) -> pair_wrap A.

Module Ops.
  Definition get_fst {A : Type} (p : pair_wrap A) : A :=
    match p with
    | mk_pair_wrap _ pv => fst pv
    end.

  Definition get_snd {A : Type} (p : pair_wrap A) : nat :=
    match p with
    | mk_pair_wrap _ pv => snd pv
    end.

  Definition make {A : Type} (a : A) (n : nat) : pair_wrap A :=
    mk_pair_wrap A (a, n).
End Ops.

Crane Separate Extraction Ops.
