From Crane Require Import Mapping.NatInt Monads.ITree.
From Crane Require Extraction.

From ITree Require Import ITree.

Import Monads.
Local Open Scope monad_scope.

(* A typeclass with a type-family member (Ref) and a polymorphic function
   member (refToIx) that references Ref.  The combination of these two
   members in the class record, together with a named Definition for the
   instance method, triggers a List.nth out-of-bounds during extraction. *)

Variant RefNat : Type -> Type :=
  | MkRefNat (A : Type) (idx : nat) : RefNat A.

Definition refToIxNat (A : Type) (r : RefNat A) : nat :=
  match r with MkRefNat _ i => i end.

Class RefClass (I : Type) : Type :=
  { Ref : Type -> Type;
    refToIx : forall A : Type, Ref A -> I }.

#[export] Instance nat_ref : RefClass nat :=
  {| Ref := RefNat; refToIx := refToIxNat |}.

Section Events.
  Variable (I : Type).
  Context `{RefClass I}.

  Variant MyEvent : Type -> Type :=
    | NewRef (v : nat) : MyEvent (Ref nat).
End Events.

Section Ops.
  Context {E : Type -> Type}.
  Context {I : Type}.
  Context `{RefClass I}.
  Context `{MyEvent I -< E}.

  Definition myNew (v : nat) : itree E (Ref nat) :=
    trigger (NewRef I v).
End Ops.

Local Notation ClassRef := (@Ref) (only parsing).
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Import PrimString.PStringNotations List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance Ref_mapping (I : Type) (H : RefClass I) (A : Type) : TypeMapping (ClassRef I H A) :=
  value_type [] (SourceType A) UnknownCopy.
#[global] Instance myNew_mapping : OperationMapping (Ref (@myNew)) :=
  pass_through [] "v" [].

Definition newOnly : itree (MyEvent nat) nat :=
  myNew 5 ;;
  Ret 0.

Crane Extraction "stmonad_nth_repro" newOnly.
