(* An instance method's parameter is erased where its type is a field of
   another class.

     static EOU<ptr> int_to_ptr(Nat i, std::any pr)

   where it should read [typename _tcI0::prov] -- Vellvm's h:12382.  The same
   declaration spells [typename _tcI0::prov] correctly elsewhere, so the type
   is available; only the method's own domain is written erased.

   The recorded negative, from the reduction's own control: making [prov] a
   plain [Definition] while keeping the carrier [(iptr * prov)%type] built
   from a class field, and keeping [PIV] parameterised by [IPtr], emits
   everything correctly.  So neither "carrier built from a class field" nor
   "instance parameterised by a class" is the variable; what distinguishes
   this case is [prov] standing as a type in the projected method's own
   {e domain}.

   Fixed: the declaration's domains were offered to the body's binders only
   when the method was a member template, which is unrelated to whether the
   declaration states more than the body.  They are now offered always, and
   outside the member-template case they only fill what the body left open --
   the body's own annotation is what its statements were generated against.

   Distinct from instance_method_param_at_class_carrier, which was the same
   shape in an instance's {e class type} and is fixed: an instance's type
   arguments are now taken per position from whichever of the two types
   states them, and a method's signature domains never pass through that
   list.

   The import list is not harness configuration -- it selects the emission
   path.  The reified mapping erases the [Monad] class, so [bind] is emitted
   against its instance rather than through the class wrapper. *)

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
  { iptr : Type ; prov : Type ; from_Z : nat -> EOU iptr ; prov_nat : prov -> nat }.

(** [int_to_ptr] returns [EOU nat], not [EOU ptr].  The carrier field is kept
    -- the instance still builds it from [iptr] and [prov] -- but the method's
    result stays concrete, so that a definition typed by a class field
    projected through a known instance, which is a separate defect, is not on
    this reduction's path.  See
    instance_carrier_unqualified_at_known_instance. *)
Class ITOP (P : IPtr) := { ptr : Type ; int_to_ptr : nat -> @prov P -> EOU nat }.

#[global] Instance PIV {IP : IPtr} : ITOP IP :=
  {| ptr := (iptr * prov)%type
   ; int_to_ptr := fun i pr => bind (from_Z i) (fun _ => ret (prov_nat pr)) |}.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; prov := bool ; from_Z := fun n => ret n
   ; prov_nat := fun b => if b then 1 else 0 |}.

(** The match is the smallest consumer that still forces [int_to_ptr] to be
    emitted. *)
Module InstanceMethodParamAtForeignClassField.
  Definition run : bool :=
    match @int_to_ptr natIPtr (@PIV natIPtr) 1 true with
    | Ok _ => true
    | Err _ => false
    end.
End InstanceMethodParamAtForeignClassField.

Set Crane Format Style "None".
Crane Extraction "instance_method_param_at_foreign_class_field" InstanceMethodParamAtForeignClassField.
