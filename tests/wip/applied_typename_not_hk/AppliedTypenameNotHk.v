(* A definition whose event family is only ever *applied*, never passed bare,
   gets that family declared as a plain `typename` while the signature keeps
   writing it applied.

   Expected: the parameter is a template template parameter, the way the
   annotated neighbours E_trigger/F_trigger already get it:

     template <template <typename> class T1, template <typename> class T2>
     std::shared_ptr<ITree<std::any>>
     h(Sum1<T1<std::any>, Sum1<AE, T2<std::any>, std::any>, std::any> x)

   Actual: both are demoted to plain (defaulted) typename and then applied:

     template <typename T1 = void, typename T2 = void>
     std::shared_ptr<ITree<std::any>>
     h(Sum1<T1<std::any>, Sum1<AE, T2<std::any>, std::any>, std::any> x)

     error: expected '>'   (at T1<std::any>, and again at T2<std::any>)

   The contrast is in the same file: F_trigger, two definitions above, is
   written with an explicit `Handler F Eff` annotation, so F occurs in a
   position the C++ signature renders and stays `template <typename> class`.
   h's type comes from case_, where E and F appear only inside the handler
   arguments -- which the callback relaxation turns into an F -- so nothing
   renders them and they fall through to plain typename with the application
   left behind.

   Reduced from Vellvm's Semantics/Handlers/Intrinsics.v:94
   (interp_intrinsics_h), which emits the same head and the same applications;
   ITree's own Recursion.interp_mrec picks up the identical shape. At Vellvm's
   scale the declaration is emitted separately from the definition and only the
   declaration gets the `= void` defaults, so there is a second error there
   that this test does not reach. *)

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
