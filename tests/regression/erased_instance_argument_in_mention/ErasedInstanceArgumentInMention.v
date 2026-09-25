(* An instance that takes an argument extraction erases -- [ParamsV {IP : IPtr}
   {IPT : IPtrTheory IP}], where [IPtrTheory] is a [Prop] class and carries no
   data.  The emitted template takes one parameter:

     template <IPtr _tcI0> struct ParamsV { ... };

   and a mention that resolves a promoted variable through it writes the Rocq
   argument list, both of them:

     typename ParamsV<natIPtr, natIPtrTheory>::PTR::ptr
     error: use of undeclared identifier 'natIPtrTheory'

   The record is faithful: [Carg (ParamsV, [natIPtr; natIPtrTheory])] is what
   the Rocq type says.  The defect is that it is taken UPSTREAM of the erasure
   and used DOWNSTREAM of it, without being projected through.  The emitter
   already decides that [ParamsV] takes one parameter; the reader has to drop
   the same arguments.

   The import list is not harness configuration -- it selects the emission
   path.

   Fixed: a proof argument is dropped where the record is taken, by
   [Extraction.arg_survives_extraction] -- the sort of the argument's type, so
   [natIPtrTheory : IPtrTheory natIPtr] goes and [natIPtr : IPtr] stays.  The
   reader has no Rocq type left to ask, and the emitter has already made this
   decision once.  An argument that names a binder keeps its position: it is
   the [Carg_unknown] the reader fills, and it cannot be typed in that
   environment anyway.  Textually, [ParamsV<natIPtr, natIPtrTheory>::ADDR]
   becomes [ParamsV<natIPtr>::ADDR]. *)

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

(* A [Prop] class: no data, so extraction erases both the class and every
   argument at it. *)
Class IPtrTheory (IP : IPtr) : Prop :=
  { to_Z_zero : @to_Z IP (@zero_iptr IP) = @to_Z IP (@zero_iptr IP) }.

Class Provenance := { prov : Type ; nil_prov : prov }.

Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.

Class Params :=
  { ADDR : Type ; zero_addr : ADDR
  ; PROV : Provenance ; PTR : @Pointer PROV ; IPTR : IPtr }.

Section withParams.
  Context {P : Params}.

  Variant dval : Type :=
    | DPtr (p : @ptr PROV PTR)
    | DIptr (i : @iptr IPTR)
    | DAddr (a : @ADDR P).
End withParams.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

#[global] Instance natIPtrTheory : IPtrTheory natIPtr :=
  {| to_Z_zero := eq_refl |}.

#[global] Instance ProvenanceV : Provenance :=
  {| prov := bool ; nil_prov := false |}.

#[global] Instance PointerV : @Pointer ProvenanceV :=
  {| ptr := (nat * bool)%type ; null := (0, false) |}.

(* Two instance arguments, and the second is erased. *)
#[global] Instance ParamsV {IP : IPtr} {IPT : IPtrTheory IP} : Params :=
  {| ADDR := nat ; zero_addr := 0
   ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module ErasedInstanceArgumentInMention.
  Definition boxed_iptr : @dval (@ParamsV natIPtr natIPtrTheory) :=
    @DIptr (@ParamsV natIPtr natIPtrTheory) (@zero_iptr natIPtr).

  Definition addr0 : @ADDR (@ParamsV natIPtr natIPtrTheory) :=
    @zero_addr (@ParamsV natIPtr natIPtrTheory).

  Definition run : nat :=
    match boxed_iptr with
    | DPtr p => fst p
    | DIptr i => @to_Z natIPtr i
    | DAddr a => a
    end.
End ErasedInstanceArgumentInMention.

Set Crane Format Style "None".
Crane Extraction "erased_instance_argument_in_mention" ErasedInstanceArgumentInMention.
