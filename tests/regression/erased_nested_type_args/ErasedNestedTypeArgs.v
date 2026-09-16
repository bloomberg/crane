(** Crane bug: when a polymorphic class method is monomorphised to [std::any],
    references to the nested alternative types of its own argument lose their
    template argument.

    [EOU_monad::bind] is emitted at [std::any], and its body reads

      std::holds_alternative<typename EOU::Raise_error>(c.v())

    where [c] has type [EOU<std::any>].  The bare [EOU] needs the argument the
    rest of the signature already has.

    Expected: [typename EOU<std::any>::Raise_error].
    Actual:   error: use of class template 'EOU' requires template arguments
              note: template is declared here

    Three occurrences here; one per [std::get]/[std::holds_alternative] on a
    constructor of the erased type. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.

Import MonadNotation.
Open Scope monad.

Variant EOU {X : Type} : Type :=
  | raise_error (s : nat) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU : clear implicits.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
     bind _ _ c k :=
       match c with
       | raise_error s => raise_error s
       | raise_ret x => k x
       end
  |}.

(* A class of operations returning into the monad, the shape of Vellvm's
   [VMemInt]: it is what forces [bind] to be emitted at [std::any]. *)
Class Ops (I : Type) : Type := { madd : I -> I -> EOU I ; mzero : I }.

#[global] Instance Ops_nat : Ops nat :=
  {| madd x y := ret (x + y) ; mzero := 0 |}.

Module ErasedNestedTypeArgs.

  Definition use (n : nat) : EOU nat := @madd nat Ops_nat n n.

End ErasedNestedTypeArgs.

Crane Extraction "erased_nested_type_args" ErasedNestedTypeArgs.
