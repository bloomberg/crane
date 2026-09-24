(* A constructor whose type parameter occurs in none of its arguments takes
   that parameter from the expected type -- and inside a bind's action, the
   expected type is the action's, not the enclosing function's.

     bind<Bool0, Dv>([]() {
       ...
       return ::EOU_monad::template ret<Bool0>(...);   // right
       return EOU<Dv>::err(...);                       // wrong: wants EOU<Bool0>
     }, ...)

   `ret` arrives through the monad's instance and resolves against the action,
   so it is instantiated correctly.  `Err`'s own `A` is unconstrained by its
   `nat` argument, so the only thing that can say what it is is the position
   the term sits in -- and the emitter reads the enclosing declaration's
   return type there instead of the type of the action being built.

   Visible only where a bind's two type arguments differ: at `bind<A, A>` the
   wrong scope and the right one name the same type, which is why a corpus
   full of `bind<Dvalue, Dvalue>` reports two sites and not two hundred.
   Reduced by the Vellvm session from `eval_int_icmp` and `eval_int_op`
   (`bind<bool, Dvalue_base>` and `bind<Z, Dvalue_base>`), where 239 of 241
   `raise_error` sites are right for exactly that reason.

   Their control -- the same function with the action at the enclosing type --
   emits the error constructor once, correctly, so the difference is the
   differing type arguments and nothing else.  Note also that wrapping the
   constructor in a definition hides the defect: a wrapper gives the type
   parameter a second place to come from. *)

From Crane Require Import Extraction.
Require Import PeanoNat.

(* An error monad whose failure constructor says nothing about the payload
   type: [A] occurs in neither [Err]'s argument nor its arity. *)
Variant EOU (A : Type) : Type :=
  | Ok : A -> EOU A
  | Err : nat -> EOU A.
Arguments Ok {A}.
Arguments Err {A}.

Definition ret {A : Type} (a : A) : EOU A := Ok a.

Definition bind {A B : Type} (m : EOU A) (k : A -> EOU B) : EOU B :=
  match m with Ok a => k a | Err c => Err c end.

Inductive Dv : Type := DvBool : bool -> Dv | DvNat : nat -> Dv.

Module ErrorCtorTypeFromEnclosingReturn.
  (* The action is [EOU bool]; the enclosing declaration returns [EOU Dv]. *)
  Definition eval_icmp (x y : nat) : EOU Dv :=
    bind (if Nat.eqb x y then ret true else Err 7)
         (fun b : bool => ret (DvBool b)).

  Definition run : nat :=
    match eval_icmp 1 1 with
    | Ok (DvBool true) => 1
    | _ => 0
    end.
End ErrorCtorTypeFromEnclosingReturn.

Crane Extraction "error_ctor_type_from_enclosing_return"
  ErrorCtorTypeFromEnclosingReturn.
