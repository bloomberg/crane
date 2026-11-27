(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A recursive function generic over an event family [E'], taking a mapped
    value whose phantom type [S] the C++ type does not mention.  Neither
    variable is spelled by the C++ type, so neither is a template parameter:
    the self-call writes no type argument, and its value is read at the type
    the declaration spells, the tree's result.  Once [S]'s filler ([void]),
    written so that [E'] could be written after it, was read as the call's
    instantiation of [S], and the typed-fit check failed. *)

From Stdlib Require Import Arith.PeanoNat List PrimString.
From ITree Require Import ITree Events.Exception.
From Crane Require Import Extraction Mapping.NatInt Monads.ITree Monads.Error Mapping.Descriptor.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** A cell whose phantom [S] its C++ type, [std::shared_ptr<A>], does not
    mention. *)
Axiom Cell : Type -> Type -> Type.

#[export] Instance cell_mapping (S A : Type) : TypeMapping (Cell S A) :=
  {| type_headers := ["memory"];
     type_cpp := Crane.Cpp.Apply "std::shared_ptr"
                   [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
     type_components :=
       [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := ReadOnlyHandle HandleByConstReference;
     type_views := NoViews (Cell S A);
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}%pstring.

Module PhantomFillerNotWritten.
Section Count.
  Context {S : Type}.

  (** Counts [n] down in [E'], passing the cell along. *)
  Fixpoint count_down {E' : Type -> Type} (c : Cell S nat) (n : nat) : itree E' nat :=
    match n with
    | O => Ret 0
    | Datatypes.S n' => r <- @count_down E' c n';; Ret (Datatypes.S r)
    end.
End Count.

(** Runs the tree: extracted as the identity. *)
Axiom run : forall {A : Type}, itree (exceptE Err) A -> A.

Definition run_count (c : Cell unit nat) (n : nat) : nat := run (count_down c n).
End PhantomFillerNotWritten.

Crane Extract Inlined Constant PhantomFillerNotWritten.run => "%a0".
Crane Extraction "phantom_filler_not_written" PhantomFillerNotWritten.
