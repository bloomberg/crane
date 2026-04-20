From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseTagMismatch.

(** BUG HYPOTHESIS: The reuse optimization mutates variant fields in-place
    when use_count() == 1 and the tail constructor has the same arity
    as the matched constructor, even when they are DIFFERENT constructors.
    This leaves the variant with the WRONG tag — the original matched
    constructor tag persists instead of changing to the tail constructor.

    The reuse optimization fires when:
    1. The scrutinee is "owned" (escapes in some code path)
    2. The tail constructor has the same arity as the matched constructor
    3. same_inductive holds (same type)
    4. use_count() == 1 at runtime

    It does NOT check that matched_ctor == tail_ctor. *)

Inductive direction :=
  | GoUp : nat -> direction
  | GoDown : nat -> direction.

(** The 'else d' branch causes d to escape (returned in tail position).
    This makes d "owned" (infer_owned_params marks it).
    The 'then' branch's match has reuse candidates because:
    - GoUp/GoDown are the same inductive (direction)
    - Both have arity 1
    But GoUp and GoDown are DIFFERENT constructors. *)
Definition id_or_flip (d : direction) (flip_flag : bool) : direction :=
  if flip_flag then
    match d with
    | GoUp n => GoDown n
    | GoDown n => GoUp n
    end
  else d.

(** test1: flip GoUp 42 -> should be GoDown 42.
    Match on the result:
    - GoUp _ => 1 (wrong, reuse bug would make this match)
    - GoDown _ => 2 (correct) *)
Definition test1 : nat :=
  match id_or_flip (GoUp 42) true with
  | GoUp _ => 1
  | GoDown _ => 2
  end.

(** test2: no flip -> should be GoUp 42 unchanged. *)
Definition test2 : nat :=
  match id_or_flip (GoUp 42) false with
  | GoUp _ => 1
  | GoDown _ => 2
  end.

(** test3: flip GoDown 100 -> should be GoUp 100. *)
Definition test3 : nat :=
  match id_or_flip (GoDown 100) true with
  | GoUp _ => 3
  | GoDown _ => 4
  end.

(** test4: use the flipped value's payload. *)
Definition test4 : nat :=
  match id_or_flip (GoUp 10) true with
  | GoUp n => n + 1000
  | GoDown n => n
  end.

End ReuseTagMismatch.

Crane Extraction "reuse_tag_mismatch" ReuseTagMismatch.
