(* Regression test: custom extraction of typeclass Type-valued field.

   When a typeclass has a Type-valued projection (Ref : Type -> Type) with
   a type mapping, the extraction's mlt_env typedef cache
   must NOT expand the constant's body, otherwise it extracts the projection to std::any. *)

From Crane Require Import Mapping.NatInt Monads.ITree.
Require Import Crane.Extraction.
From ITree Require Import ITree.

Import Monads.
Local Open Scope monad_scope.

Variant RefNat : Type -> Type :=
  | MkRef (A : Type) (idx : nat) : RefNat A.

Class RefClass (I : Type) : Type :=
  { Ref : Type -> Type;
    mkRef : forall A, I -> Ref A }.

#[export] Instance nat_ref : RefClass nat :=
  {| Ref := RefNat;
     mkRef := fun A i => MkRef A i |}.

Section Ops.
  Context {I : Type}.
  Context `{RefClass I}.

  Definition newRef (idx : I) : itree void1 (Ref nat) :=
    Ret (mkRef nat idx).
End Ops.



(* Concrete instantiation: returns Ref nat = uint64_t.
   With the bug, the internal variable becomes std::any causing a type
   mismatch compile error. *)
Definition test_new : itree void1 (Ref nat) :=
  r <- newRef 5 ;;
  Ret r.

Local Notation ClassRef := (@Ref) (only parsing).
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Import PrimString.PStringNotations List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance Ref_mapping (I : Type) (H : RefClass I) (A : Type) : TypeMapping (ClassRef I H A) :=
  value_type [] (SourceType A) UnknownCopy.
#[global] Instance newRef_mapping : OperationMapping (Ref (@newRef)) :=
  effect_cpp [] ["idx"] (WithBody "" "%result = %arg(idx)").

Crane Extraction "custom_typeclass_type" test_new.
