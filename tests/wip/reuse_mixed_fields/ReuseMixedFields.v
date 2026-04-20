From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseMixedFields.

(** BUG: The reuse optimization fires when matched_ctor != tail_ctor
    as long as they have the same arity. When field TYPES differ,
    the reuse path assigns values of the tail ctor's field types
    into the matched ctor's fields. If field types are compatible
    (same C++ type), the data is correct but the tag is wrong.
    If field types differ, this could cause type confusion. *)

(** Two constructors with same arity but different field types. *)
Inductive payload :=
  | AsNat : nat -> nat -> payload
  | AsPair : nat -> nat -> payload.

(** Forces d to be owned through the else branch.
    The match branch has reuse candidates: both AsNat and AsPair
    have arity 2. *)
Definition swap_tag_or_id (p : payload) (do_swap : bool) : payload :=
  if do_swap then
    match p with
    | AsNat a b => AsPair b a    (* swap fields AND tag *)
    | AsPair a b => AsNat b a
    end
  else p.

(** test1: swap AsNat 10 20 -> should be AsPair 20 10.
    With reuse bug: variant stays AsNat, fields are 20, 10.
    Match sees AsNat -> returns first field + 1000 = 1020.
    Correct: Match sees AsPair -> returns first field = 20. *)
Definition test1 : nat :=
  match swap_tag_or_id (AsNat 10 20) true with
  | AsNat a _ => a + 1000
  | AsPair a _ => a
  end.

(** test2: chain two swaps. Should be identity.
    swap(swap(AsNat 5 6)) = swap(AsPair 6 5) = AsNat 5 6.
    With reuse bug: first swap returns AsNat 6 5 (wrong tag),
    second swap matches AsNat -> returns AsNat 5 6 (right tag but
    swapped fields). *)
Definition test2 : nat :=
  match swap_tag_or_id (swap_tag_or_id (AsNat 5 6) true) true with
  | AsNat a b => a * 10 + b
  | AsPair a b => a * 10 + b + 1000
  end.

End ReuseMixedFields.

Crane Extraction "reuse_mixed_fields" ReuseMixedFields.
