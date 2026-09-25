(* A declaration whose OWN TYPE never mentions the instance, and whose body
   applies it:

     Definition check (_ : unit) : nat :=
       let r := @runS (@ParamsV natIPtr) 0 in
       match r with inl _ => 0 | inr dv => @to_nat (@ParamsV natIPtr) dv end.

   [unit -> nat] holds no applied class at any depth, so searching the
   declaration's type finds nothing.  The instance is in the application, and
   the dictionary argument is erased before the emitter sees the body, so the
   ML term does not hold it either.  The local binder's type -- [nat + dval] --
   is what carries the dependence, and it is spelled at the file-scope erased
   aliases:

     typename Sum<Nat, Dval<ptr, iptr>>::Inr

   while [runS] returns the resolved instantiation.  Every mention here is in a
   scope that HAS the instance; it is available and simply not used.

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
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Class IPtr := { iptr : Type ; zero_iptr : iptr ; to_Z : iptr -> nat }.
Class Provenance := { prov : Type ; nil_prov : prov }.
Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.
Class Params := { ADDR : Type ; zero_addr : ADDR
  ; PROV : Provenance ; PTR : @Pointer PROV ; IPTR : IPtr }.

Section withParams.
  Context {P : Params}.
  Variant dval : Type := | DPtr (p : @ptr PROV PTR) | DIptr (i : @iptr IPTR).

  Definition runS (n : nat) : sum nat dval := inr (DIptr (@zero_iptr IPTR)).

  Definition to_nat (d : dval) : nat :=
    match d with DPtr _ => 0 | DIptr i => @to_Z IPTR i end.
End withParams.

#[global] Instance natIPtr : IPtr := {| iptr := nat ; zero_iptr := 0 ; to_Z := fun n => n |}.
#[global] Instance ProvenanceV : Provenance := {| prov := bool ; nil_prov := false |}.
#[global] Instance PointerV : @Pointer ProvenanceV := {| ptr := (nat * bool)%type ; null := (0, false) |}.
#[global] Instance ParamsV {IP : IPtr} : Params :=
  {| ADDR := nat ; zero_addr := 0 ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module InstanceOnlyInBodyApplication.
  (* The type says [unit -> nat]; only the body says [ParamsV natIPtr]. *)
  Definition check (_ : unit) : nat :=
    let r := @runS (@ParamsV natIPtr) 0 in
    match r with
    | inl e => e
    | inr dv => @to_nat (@ParamsV natIPtr) dv
    end.

  Definition run : nat := check tt.
End InstanceOnlyInBodyApplication.

Set Crane Format Style "None".
Crane Extraction "instance_only_in_body_application" InstanceOnlyInBodyApplication.
