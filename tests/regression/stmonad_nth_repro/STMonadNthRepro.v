From Crane Require Import Mapping.NatIntStd Monads.ITree.
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

Crane Extract Inlined Constant Ref => "%t0".
Crane Extract Inlined Constant myNew => "%a0".

Definition newOnly : itree (MyEvent nat) nat :=
  myNew 5 ;;
  Ret 0.

Crane Extraction "stmonad_nth_repro" newOnly.
