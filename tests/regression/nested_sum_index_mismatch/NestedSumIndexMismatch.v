(** Crane bug: a family-sum alias ([AllE := aE +' bE +' cE]) applied at an
    index expands with the *inner* sums indexed [std::any], while matches
    and constructors on the same value index them at the real index.

    Observed (0b9b536f0):
      c_of(const Sum1<AE, Sum1<BE, cE, std::any>, T1> &e)   // parameter: inner index std::any
        ... std::holds_alternative<typename Sum1<BE, cE, T1>::Inl1>(a0.v())   // match: inner index T1
      c_of<std::monostate>(
          Sum1<AE, Sum1<BE, cE, std::any>, std::monostate>::inr1(
              Sum1<BE, cE, std::monostate>::inr1(...)))                      // ctor: inner index monostate
    In ITree, [(E1 +' (E2 +' E3)) X = sum1 E1 (E2 +' E3) X], and [inr1]'s
    payload is [sum1 E2 E3 X]: the same X at every level.  Diagnostic
    (libc++):
      error: static assertion failed due to requirement 'value != __not_found':
             type not found in type list
    (One consistent spelling is needed; the alias's [std::any] inside is the
    odd one out.)

    Reduced from Vellvm, [Semantics/Denotation.v:832]
    [exc_of_event {X} (e : CFGEtop X) : option exc] (match eight [inr1]s
    deep): the two remaining find_index static_asserts on 0b9b536f0. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module NestedSumIndexMismatch.
  Variant aE : Type -> Type := A : aE nat.
  Variant bE : Type -> Type := B : bE nat.
  Variant cE : Type -> Type := C : nat -> cE unit.

  Definition AllE := aE +' bE +' cE.

  (* Vellvm's [exc_of_event {X} (e : CFGEtop X) : option exc]: a match two
     [inr1]s deep, generic in the index X. *)
  Definition c_of {X : Type} (e : AllE X) : option nat :=
    match e with
    | inr1 (inr1 (C n)) => Some n
    | _ => None
    end.

  Definition is_three : bool :=
    match c_of (inr1 (inr1 (C 3)) : AllE unit) with Some n => Nat.eqb n 3 | None => false end.
End NestedSumIndexMismatch.

Crane Extraction "nested_sum_index_mismatch" NestedSumIndexMismatch.
