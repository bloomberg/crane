(* An inductive declared under a [Context] carries a constructor field whose
   type is a class field of that context variable, and is emitted as a plain
   non-template struct with the field erased to [std::any].

   [dval] depends on [IP] through [@ptr ProvenanceV PointerV], so it has no
   meaning independent of one -- but nothing in the emitted struct says so:

     struct Dval { struct DPtr { ptr p; }; ... };   // ptr == std::any

   The value really is a [std::any] at every use, so a consumer that names the
   type correctly cannot be satisfied by any amount of resolution at the use.
   The fix has to parameterise the inductive, not resolve a name: the struct
   needs the template parameter the section variable became, and every mention
   of it has to pass one.

   Distinct from class_field_alias_at_call_argument, which is the same
   diagnostic with a different cause -- there the value was a parameter and
   the callee's type could be read off the term.  A type error names the two
   types that met, not where either came from.

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

  (* The inductive is declared under the section's [Context], and one of its
     constructors carries a field of that context variable's class. *)
  Variant dval : Type :=
    | DPtr (p : @ptr ProvenanceV PointerV)
    | DNat (n : nat).
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module InductiveFieldAtSectionClassField.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition boxed : @dval natIPtr := @DPtr natIPtr the_null.

  Definition run : nat :=
    match boxed with
    | DPtr p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
    | DNat n => n
    end.
End InductiveFieldAtSectionClassField.

Set Crane Format Style "None".
Crane Extraction "inductive_field_at_section_class_field" InductiveFieldAtSectionClassField.
