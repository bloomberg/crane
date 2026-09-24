(* A class field used as a type at a call argument resolves through the
   file-scope alias, while the callee now demands the instance's real type.

   [PIV]'s methods are spelled correctly since
   promoted_var_of_specialised_instance_argument: [ptr_to_int] takes a
   [typename PointerV<_tcI0>::ptr].  A caller that holds a [ptr] does not --
   at module scope there is no instance in sight, so the promoted variable
   falls back to [using ptr = std::any;] and the two sides disagree.  The
   mismatch was invisible while both sides were [std::any].

   This is the second half of the same defect: there the resolution was read
   off the term that inhabits the type, here the type stands alone in a
   parameter.

   The import list is not harness configuration -- it selects the emission
   path. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monad.

Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type := | Ok : A -> EOU A | Err : nat -> EOU A.
Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret  := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Class IPtr :=
  { iptr : Type ; zero_iptr : iptr ; from_Z : nat -> EOU iptr
  ; to_Z : iptr -> nat }.

(* [nil_prov] and [null] are not decoration: without a second field an
   instance of a one-Type-field class generates no struct at all, and the
   defect needs the target to exist and be right. *)
Class Provenance := { prov : Type ; nil_prov : prov }.

Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.

Class PI (P : Provenance) (PT : Pointer P) :=
  { ptr_to_int : @ptr P PT -> nat
  ; int_to_ptr : nat -> @prov P -> EOU (@ptr P PT) }.

Section withIPtr.
  Context {IP : IPtr}.

  #[global] Instance ProvenanceV : Provenance :=
    {| prov := bool ; nil_prov := false |}.

  #[global] Instance PointerV : @Pointer ProvenanceV :=
    {| ptr := (iptr * prov)%type ; null := (zero_iptr, nil_prov) |}.

  #[global] Instance PIV : @PI ProvenanceV PointerV :=
    {| ptr_to_int := fun p => to_Z (fst p)
     ; int_to_ptr := fun i pr => bind (from_Z i) (fun a => ret (a, pr)) |}.
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module ClassFieldAliasAtCallArgument.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  (* The parameter is the class field, written at the instance -- and nothing
     in the emitted signature says so: it resolves through the file-scope
     alias, while the method it is handed to now demands the real type. *)
  Definition use (p : @ptr ProvenanceV (@PointerV natIPtr)) : nat :=
    @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p.

  Definition run : nat := use the_null.
End ClassFieldAliasAtCallArgument.

Set Crane Format Style "None".
Crane Extraction "class_field_alias_at_call_argument" ClassFieldAliasAtCallArgument.
