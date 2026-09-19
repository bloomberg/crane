(* A polymorphic helper whose event argument is absurd ([FailE void]) gets
   promoted to a method on the event struct.  Promotion drops the type
   parameter the body still mentions, and the caller is rewritten into an
   immediately-invoked lambda whose parameters lost their types and which is
   then invoked with no arguments at all.

   Expected: [cast_] to declare every template parameter its body uses, and
             [raise0] to call it with the event and the receiver.
   Actual (from the generated header):

       template <typename T2> std::shared_ptr<ITree<T2>> cast_() const {
         T1 _x = itree_trigger(this-deref);        // T1 is not a parameter
         ...
       template <typename T1, typename T2>
       std::shared_ptr<ITree<T2>> raise0(const Nat &) {   // name dropped
         return [](const &_x0, const auto &_x1) {         // no type specifier
           return _x1.template cast_<T2>(_x0); }();       // no arguments
       }

     error: unknown type name 'T1'
     error: a type specifier is required for all declarations
     error: no matching function for call to object of type '(lambda ...)'
     error: unused parameter '_x0' [-Werror,-Wunused-parameter]

   In Vellvm this is the [raise]/[raiseUB] cluster, 40 errors, from
   rocq/Semantics/LLVMEvents.v:176-193 via Utils/ITreeUtil.v:6. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Definition cast' {E : Type -> Type} {A : Type} `{FailE -< E} (e : FailE void)
  : itree E A :=
  ITree.bind (trigger e) (fun v : void => match v with end).

Definition raise {E} {A} `{FailE -< E} (n : nat) : itree E A :=
  cast' (Throw tt).

Module PromotedMethodLeaksParam.
  Definition use (l : list nat) : itree FailE nat :=
    match l with
    | [] => raise 0
    | x :: _ => Ret x
    end.
End PromotedMethodLeaksParam.

Crane Extraction "promoted_method_leaks_param" PromotedMethodLeaksParam.
