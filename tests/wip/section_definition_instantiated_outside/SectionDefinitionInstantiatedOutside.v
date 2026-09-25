(* A [Definition] OUTSIDE a Section that instantiates a [Definition] INSIDE it,
   by applying the Section's [Context] variable to a concrete instance:

     Definition eqb0 := @inner_eqb (@ParamsV natIPtr).

   Neither body mentions [ParamsV] or the instance; the instance appears only
   in the application at the outer [Definition].  The inductive the inner
   definition ranges over has TWO promoted variables, reached through the
   context variable as [PTR::ptr] and [IPTR::iptr], and they should travel by
   the identical path.  One arrives:

     Dval<typename ParamsV<natIPtr>::PTR::ptr, iptr>

   The second is the file-scope erased alias.  Same instance, same head, one
   variable resolved and one not, so whatever supplies the first is not being
   asked for the second -- or is asked and answers once.

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
  { iptr : Type ; zero_iptr : iptr ; to_Z : iptr -> nat }.

Class Provenance := { prov : Type ; nil_prov : prov }.

Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.

Class Params :=
  { ADDR : Type ; zero_addr : ADDR
  ; PROV : Provenance ; PTR : @Pointer PROV ; IPTR : IPtr }.

Section withParams.
  Context {P : Params}.

  Variant dval : Type :=
    | DPtr (p : @ptr PROV PTR)
    | DIptr (i : @iptr IPTR).

  (* Inside the Section, and mentioning no instance: everything it knows about
     [dval] comes from [P]. *)
  Definition inner_eqb (d : dval) : nat :=
    match d with DPtr _ => 0 | DIptr i => @to_Z IPTR i end.

  Definition inner_zero : dval := DIptr (@zero_iptr IPTR).
End withParams.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; to_Z := fun n => n |}.

#[global] Instance ProvenanceV : Provenance :=
  {| prov := bool ; nil_prov := false |}.

#[global] Instance PointerV : @Pointer ProvenanceV :=
  {| ptr := (nat * bool)%type ; null := (0, false) |}.

#[global] Instance ParamsV {IP : IPtr} : Params :=
  {| ADDR := nat ; zero_addr := 0
   ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module SectionDefinitionInstantiatedOutside.
  (* The application is the only place the instance appears. *)
  Definition eqb0 := @inner_eqb (@ParamsV natIPtr).
  Definition zero0 := @inner_zero (@ParamsV natIPtr).

  Definition run : nat := eqb0 zero0.
End SectionDefinitionInstantiatedOutside.

Set Crane Format Style "None".
Crane Extraction "section_definition_instantiated_outside" SectionDefinitionInstantiatedOutside.
