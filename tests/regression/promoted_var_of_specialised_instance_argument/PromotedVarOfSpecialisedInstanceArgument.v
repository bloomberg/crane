(* A promoted type variable belonging to a concrete instance argument has
   nowhere to resolve, because the argument was specialised away.

   [PI] is parameterised by a [Provenance] and a [Pointer], and both are given
   concretely at the instance.  Crane specialises them out of the generated
   struct's template parameters, so [prov] and [ptr] -- their promoted vars --
   keep their names and lose the path that gave them meaning, falling back to
   the file-scope [using prov = std::any;].  [iptr] is the control: it comes
   from the surviving [Context {IP : IPtr}], reaches C++ as [_tcI0], and
   resolves correctly.  One declaration, two promoted vars, and the only
   difference is whether the instance that owns each one survived as a
   template parameter.

   Both targets exist already and are correct -- [ProvenanceV::prov] and
   [PointerV<_tcI0>::ptr] are emitted -- so nothing has to be generated, only
   named.

   Distinct from instance_carrier_unqualified_at_known_instance, which is the
   same defect one step in: there the instance is named in the term that
   inhabits the type, and the resolution can be read off the projection's
   scrutinee.  Here the instances that own the erased names are not in the
   term at all; they are the class arguments of the enclosing instance.

   The import list is not harness configuration -- it selects the emission
   path.

   Fixed in two halves, because the defect has two sites.

   At the instance's own definition, the class arguments are recorded where
   they are still written down -- the Rocq type, at extraction -- and the
   promoted variables they own are resolved through them, so [PIV]'s methods
   read [typename PointerV<_tcI0>::ptr] and [typename ProvenanceV::prov].

   At a use, the match over the call's result annotated [EOU<std::any>]: the
   annotation states the inductive and leaves its argument open, and the
   projection that produces the value is an [MLcase], not an application, so
   the reader that would have supplied the missing argument never looked at
   it.  The class declares the projected field's type, and that is now what
   fills the hole -- erased positions only, and only with a spelling this
   scope can resolve. *)

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

Module PromotedVarOfSpecialisedInstanceArgument.
  (* Forces the two specialised-away instances to be emitted, as they are at
     the real site, so the resolution targets exist and are right. *)
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition run : nat :=
    match @int_to_ptr ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) 1 true with
    | Ok p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
    | Err _ => 0
    end.
End PromotedVarOfSpecialisedInstanceArgument.

Set Crane Format Style "None".
Crane Extraction "promoted_var_of_specialised_instance_argument" PromotedVarOfSpecialisedInstanceArgument.
