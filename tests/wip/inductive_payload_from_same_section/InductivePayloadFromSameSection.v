(* An inductive declared under a [Context] carries a constructor field whose
   type is *another inductive from the same Section* -- no class field of the
   context variable appears in it at all.

   [dnest] mentions [dval], and [dval] mentions [@ptr ProvenanceV PointerV];
   so [dnest] depends on [IP] just as surely, one hop further away.  A
   recogniser that asks "is this constructor field a class field of the context
   variable" answers yes for [dval] and no for [dnest], which parameterises the
   source and leaves everything reachable from it behind: [dnest] stays a plain
   struct whose field is [Dval<ptr>] at the erased file-scope aliases, and every
   scope that destructures one gets the erased instantiation back.

   The property is the transitive closure of the one-hop test over constructor
   payloads.  Follows inductive_field_at_section_class_field, which fixed the
   one hop.

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

  (* This one names no class field: its payload is the inductive above. *)
  Variant dnest : Type :=
    | DBox (d : dval)
    | DUnit.
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module InductivePayloadFromSameSection.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition nested : @dnest natIPtr := @DBox natIPtr (@DPtr natIPtr the_null).

  Definition run : nat :=
    match nested with
    | DBox d =>
      match d with
      | DPtr p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
      | DNat n => n
      end
    | DUnit => 0
    end.
End InductivePayloadFromSameSection.

Set Crane Format Style "None".
Crane Extraction "inductive_payload_from_same_section" InductivePayloadFromSameSection.
