(* A body that names TWO instances which answer the same promoted variable
   differently.  [natIPtr] says [iptr := nat], [boolIPtr] says [iptr := bool],
   and [run] mentions declarations at both:

     Definition a0 := @inner natIPtr.    (* dval, at iptr = nat *)
     Definition b0 := @inner boolIPtr.   (* dval, at iptr = bool *)
     Definition run := eq_n (to_nat a0) (to_nat b0).

   Every other test in this family has a single right answer and asks whether
   the resolver finds it.  This one has two, so the only right answer is
   NEITHER: the resolver must leave the name erased and let the values reach
   their uses at the spellings their own declarations carry.  Picking one would
   spell [a0]'s type onto [b0].

   This exercises the ambiguity filter in [Gen_decls], which drops a promoted
   name two instances answer with different types.  Across the whole test suite
   that filter currently fires zero times, so a change that broke it would be
   silent; this is the case that makes it loud.

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

Section withIPtr.
  Context {IP : IPtr}.

  Variant dval : Type := | DIptr (i : @iptr IP) | DNat (n : nat).

  Definition inner : dval := DIptr (@zero_iptr IP).

  Definition to_nat (d : dval) : nat :=
    match d with DIptr i => @to_Z IP i | DNat n => n end.
End withIPtr.

(* Two instances, disagreeing on [iptr]. *)
#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; to_Z := fun n => n |}.

#[global] Instance boolIPtr : IPtr :=
  {| iptr := bool ; zero_iptr := false ; to_Z := fun b => if b then 1 else 0 |}.

Module TwoInstancesDisagreeOnPromotedName.
  Definition a0 := @inner natIPtr.
  Definition b0 := @inner boolIPtr.

  (* One body, both instances, and local bindings whose types the emitter has
     to spell for itself. *)
  Definition run : nat :=
    let x := @inner natIPtr in
    let y := @inner boolIPtr in
    @to_nat natIPtr x + @to_nat boolIPtr y + @to_nat natIPtr a0
      + @to_nat boolIPtr b0.
End TwoInstancesDisagreeOnPromotedName.

Set Crane Format Style "None".
Crane Extraction "two_instances_disagree_on_promoted_name" TwoInstancesDisagreeOnPromotedName.
