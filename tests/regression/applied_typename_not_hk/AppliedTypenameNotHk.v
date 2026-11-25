(** A definition whose event family is only ever applied, never passed
    bare, combined with [case_]; reduced from Vellvm's
    Semantics/Handlers/Intrinsics.v:94 (interp_intrinsics_h).

    Fixed, in three places:
    - [h]'s result index is undeducible, so its declaration erases it and
      [h] returns [shared_ptr<ITree<std::any>>] where [use] promises the tree
      at [nat].  Extraction records the coercion, and the value is now read
      back with [crane_convert] (to [crane_cast_to]) where the two types
      differ only in the box inside a mapped type.
    - [@handle Eff], methodified onto [AE] and named unapplied, was written
      [_x.handle()]: the index the method's head is written at is not one
      the use instantiates.  It is the erased instantiation, so the value
      is [_x.template handle<crane::obj>()].
    - [handle]'s body returned [itree_ret(a0)], an [ITree<Nat>], at its
      index [T2]; the value is converted at the index first. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
Import ITreeNotations.
Open Scope itree_scope.

Variant AE : Type -> Type := | A0 : nat -> AE nat.

Definition handle {E} : AE ~> itree E :=
  fun _ e => match e with A0 n => Ret n end.

Section P.
  Variable E F : Type -> Type.
  Notation Eff := (E +' AE +' F).

  (* annotated: E and F are rendered, and come out template-template *)
  Definition E_trigger : Handler E Eff := fun _ e => trigger e.
  Definition F_trigger : Handler F Eff := fun _ e => trigger e.

  (* unannotated: type comes from case_, E and F only ever applied *)
  Definition h := case_ E_trigger (case_ (@handle Eff) F_trigger).
End P.

Module AppliedTypenameNotHk.
  Definition use (n : nat) : itree (AE +' AE +' AE) nat :=
    h AE AE nat (inl1 (A0 n)).
End AppliedTypenameNotHk.

Crane Extraction "applied_typename_not_hk" AppliedTypenameNotHk.
