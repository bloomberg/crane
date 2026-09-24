(* An error constructor inside a bind's action is built at the enclosing
   declaration's result type instead of the action's, when the bind is
   reached through a monad instance.

     return EOU<Dv>::err(7);    // wanted EOU<Bool0>::err(7)

   giving `return type 'EOU<Dv>' must match previous return type
   'EOU<Bool0>' when lambda expression has unspecified explicit return type`
   -- Vellvm's h:23085, against a `bind<bool, Dvalue_base>`.

   [Err]'s type parameter occurs in neither of its arguments, so the only
   thing that can say what to build it at is the position it is written into.
   Inside the action that position is the action's type, [EOU bool]; the
   expectation in hand at the constructor is the declaration's, [EOU Dv].

   The neighbouring [error_ctor_type_from_enclosing_return] is the same
   defect with the bind written as a plain definition, and it passes: the
   call comes out [ret<Bool0>] and the action's type reaches the
   constructor.  Routing the same term through an [ExtLib] [Monad] instance
   -- [EOU_monad::template bind<bool, Dv>], which is how Vellvm reaches it --
   is the whole difference, and the distance between the bind and the
   constructor is not (a five-branch match between them changes nothing).

   Worth recording how that was established, since it is the trap this test
   exists to close: a reduction and its control agree on everything except
   the variable under study, so if the cause is in what they share, the pair
   reproduces the symptom and localises nothing.  The instance route was held
   constant and wrong in both arms of the first reduction. *)

From Crane Require Import Extraction.
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

Module ErrorCtorThroughMonadInstance.
  (* The action is [EOU bool]; the declaration returns [EOU Dv]. *)
  Definition eval_icmp (x y : nat) : EOU Dv :=
    b <- (if Nat.eqb x y then ret true else Err 7) ;; ret (DvBool b).

  Definition run : nat :=
    match eval_icmp 1 1 with
    | Ok (DvBool true) => 1
    | _ => 0
    end.
End ErrorCtorThroughMonadInstance.

Crane Extraction "error_ctor_through_monad_instance"
  ErrorCtorThroughMonadInstance.
