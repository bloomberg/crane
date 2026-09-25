(* A Section [Definition] instantiated outside the Section, whose type holds the
   Section's inductive inside a CONTAINER rather than at the conclusion's head:

     Definition w0 := @wrap (@ParamsV natIPtr).   (* dval -> option (list dval) *)
     Definition l0 := @dlist (@ParamsV natIPtr).  (* list dval *)

   [dval] has two promoted variables, and every mention in these declarations'
   own signatures should be spelled through [ParamsV<natIPtr>].  Instead the
   body of [run] builds its argument at the erased file-scope aliases:

     w0(Dval<ptr, typename natIPtr::iptr>::diptr(natIPtr::zero_iptr()))

   and the generated cross-instantiation converting constructor
   [Dval(const Dval<_U0,_U1>&)] then has to assign a [const std::any] payload
   into a [std::pair<Nat, bool>] field:

     error: no viable conversion from 'const std::any' to 'std::pair<Nat, bool>'

   [iptr] is resolved because the body names [natIPtr] directly; [ptr] is not,
   because nothing the body names says anything about it.  What does say it is
   [w0]'s own type -- but only under [option] and [list], not at its head.

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

  Definition dlist : list dval := cons (DIptr (@zero_iptr IPTR)) nil.

  Fixpoint sum_list (l : list dval) : nat :=
    match l with
    | nil => 0
    | cons d r => (match d with DPtr _ => 0 | DIptr i => @to_Z IPTR i end) + sum_list r
    end.

  Definition wrap (d : dval) : option (list dval) := Some (cons d nil).
End withParams.

#[global] Instance natIPtr : IPtr := {| iptr := nat ; zero_iptr := 0 ; to_Z := fun n => n |}.
#[global] Instance ProvenanceV : Provenance := {| prov := bool ; nil_prov := false |}.
#[global] Instance PointerV : @Pointer ProvenanceV := {| ptr := (nat * bool)%type ; null := (0, false) |}.
#[global] Instance ParamsV {IP : IPtr} : Params :=
  {| ADDR := nat ; zero_addr := 0 ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module ErasedDvalInContainer.
  Definition l0 := @dlist (@ParamsV natIPtr).
  Definition s0 := @sum_list (@ParamsV natIPtr).
  Definition w0 := @wrap (@ParamsV natIPtr).
  Definition run : nat := s0 l0 + match w0 (DIptr (@zero_iptr natIPtr)) with Some l => s0 l | None => 0 end.
End ErasedDvalInContainer.

Set Crane Format Style "None".
Crane Extraction "erased_dval_in_container" ErasedDvalInContainer.
