(* An instance that takes an instance -- [ParamsV {IP : IPtr}] -- used at a
   concrete argument.  The resolution a declaration's own type supplies spells
   the instance at itself:

     typename ParamsV<ParamsV>::ADDR

   and a bare [typename ParamsV::PTR::ptr] elsewhere, which needs arguments.

   The cause is what gets recorded.  [Table.add_instance_class_shape] keeps a
   head and an ARITY -- [(ParamsV, 1)] -- and never the argument, so
   [Gen_decls.ind_type_resolutions] has to invent one for [own_instances] and
   invents the head again.  Every earlier fix in this series got away with it
   because the instances were applied to nothing, or to exactly the arguments
   the reader already held.

   Fix the shape record before the reader: a shape is a tree, not a pair.

   The import list is not harness configuration -- it selects the emission
   path.

   Fixed: a recorded class argument is now [Table.class_arg] -- a head and its
   arguments, recursively, with [Carg_unknown] for a head that is not a
   constant -- so [@ParamsV natIPtr] and [@ParamsV IP] are no longer the same
   record.  [Gen_decls.class_arg_type] spells one back, filling a
   [Carg_unknown] positionally from the instances the reader holds, which is
   the old behaviour and now only the fallback.  Textually,
   [ParamsV<ParamsV>::ADDR] becomes [ParamsV<natIPtr>::ADDR] and the bare
   [ParamsV::PTR::ptr] gains its argument.

   And a second, smaller half: the type a match spells is resolved by the
   scrutinee's declaration, not by the match body, so
   [Gen_decls.with_body_resolutions] reads [ind_type_resolutions] of the
   globals the body names -- last, because an instance the body mentions
   directly is the nearer answer. *)

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

(* [ADDR] is not decoration: a class all of whose fields are instances is
   erased outright, and the defect needs the instance struct to exist. *)
Class Params :=
  { ADDR : Type ; zero_addr : ADDR
  ; PROV : Provenance ; PTR : @Pointer PROV ; IPTR : IPtr }.

Section withParams.
  Context {P : Params}.

  (* Each payload names a field of a different instance field of [P]. *)
  Variant dval : Type :=
    | DPtr (p : @ptr PROV PTR)
    | DIptr (i : @iptr IPTR)
    | DAddr (a : @ADDR P).
End withParams.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

#[global] Instance ProvenanceV : Provenance :=
  {| prov := bool ; nil_prov := false |}.

#[global] Instance PointerV : @Pointer ProvenanceV :=
  {| ptr := (nat * bool)%type ; null := (0, false) |}.

(* The instance takes its [IPtr] rather than fixing it, which is what
   [ParamsV<IPZ>] is in the artifact. *)
#[global] Instance ParamsV {IP : IPtr} : Params :=
  {| ADDR := nat ; zero_addr := 0
   ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module NestedInstanceFieldResolution.
  Definition boxed_ptr : @dval (@ParamsV natIPtr) := @DPtr (@ParamsV natIPtr) (@null ProvenanceV PointerV).
  Definition boxed_iptr : @dval (@ParamsV natIPtr) := @DIptr (@ParamsV natIPtr) (@zero_iptr natIPtr).

  (* Forces the instance struct to be emitted: nothing else in the module
     uses [ParamsV] as a value. *)
  Definition addr0 : @ADDR (@ParamsV natIPtr) := @zero_addr (@ParamsV natIPtr).

  Definition run : nat :=
    match boxed_iptr with
    | DPtr p => fst p
    | DIptr i => @to_Z natIPtr i
    | DAddr a => a
    end.
End NestedInstanceFieldResolution.

Set Crane Format Style "None".
Crane Extraction "nested_instance_field_resolution" NestedInstanceFieldResolution.
