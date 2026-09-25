(* A Rocq [Record] declared under the same [Context], whose field is an
   application of a type-level alias from that Section:

     struct frame { std::pair<iptr, bool> fptr; dbox<ptr> vars; };

   where [iptr] and [ptr] are the file-scope erased aliases.

   The alias is parameterised correctly now, so the field is the only thing
   left spelling the erased name, and a value built at the resolved
   instantiation does not convert to the record.

   Distinct from type_alias_of_section_inductive one category over again: the
   closure reaches an alias from a payload, but it never runs over a record's
   payloads at all -- [fold_type_body_types] skips the Record and TypeClass
   kinds.  Skipping TypeClass is right, since a class's fields are the
   promoted variables themselves; skipping Record is not.

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

  Definition dbox : Type := (dval * nat)%type.

  (* A Record whose field is an application of the alias above. *)
  Record frame : Type :=
    Frame { fptr : @ptr ProvenanceV PointerV ; vars : dbox }.
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module RecordFieldOfSectionAlias.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition packed : @dbox natIPtr := (@DPtr natIPtr the_null, 7).

  Definition fr : @frame natIPtr := @Frame natIPtr the_null packed.

  Definition run : nat :=
    @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr)
      (@fptr natIPtr fr) +
    match fst (@vars natIPtr fr) with
    | DPtr p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
    | DNat n => n
    end.
End RecordFieldOfSectionAlias.

Set Crane Format Style "None".
Crane Extraction "record_field_of_section_alias" RecordFieldOfSectionAlias.
