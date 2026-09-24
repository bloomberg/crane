(* The same defect as [error_ctor_through_monad_instance], reached by the
   route Vellvm actually takes.

   With [Monads.ITreeReified] in scope the [Monad] class is erased, so a
   [bind] is not emitted through the class wrapper ([Monad0::template
   bind<EOU_monad, ...>]) but directly against the instance
   ([EOU_monad::template bind<Bool0, Dv>]) -- {!project_through_instance},
   a second call-emission site that computed no expected type for its
   operands at all.  The action is then built at the enclosing
   declaration's result type:

     return EOU<Dv>::err(7);    // wanted EOU<Bool0>::err(7)

   which is Vellvm's h:23085, spelled against a [bind<bool, Dvalue_base>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad.
Require Import PeanoNat.

Import MonadNotation.
Local Open Scope monad_scope.

Variant EOU (A : Type) : Type :=
  | Ok : A -> EOU A
  | Err : nat -> EOU A.
Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Inductive Dv : Type := DvBool : bool -> Dv | DvNat : nat -> Dv.

Module ErrorCtorThroughReifiedInstance.
  (* The action is [EOU bool]; the declaration returns [EOU Dv]. *)
  Definition eval_icmp (x y : nat) : EOU Dv :=
    b <- (if Nat.eqb x y then ret true else Err 7) ;; ret (DvBool b).

  Definition run : nat :=
    match eval_icmp 1 1 with
    | Ok (DvBool true) => 1
    | _ => 0
    end.
End ErrorCtorThroughReifiedInstance.

Crane Extraction "error_ctor_through_reified_instance"
  ErrorCtorThroughReifiedInstance.
