(* An instance field body resolves its associated type, and a lambda inside
   that body does not.

   [assoc_type_erased_in_body] fixed the direct case: an instance's field
   bodies are now generated under the resolution map its own class parameter
   supplies, so [null] writes [_tcI0::zero_iptr()] where it used to write
   [std::any(_tcI0::zero_iptr())].  This is the same disagreement one lambda
   deeper -- the construction is not in the field body but in a function
   passed from it.

   Vellvm, [PIV::int_to_ptr] at [vellvm_bench.h:12393], survives the fix with
   the wrap intact:

     static EOU<ptr> int_to_ptr(Z i, std::any pr) {
       return EOU_monad::template bind<
           typename _tcI0::iptr,
           std::pair<typename _tcI0::iptr, std::optional<List::list<N>>>>(
           _tcI0::from_Z(std::move(i)), [=](const auto &a) mutable {
             return EOU_monad::template ret<...>(
                 std::make_pair(std::any(a), std::any(pr)));

   The signature names [typename _tcI0::iptr] twice; the [make_pair] inside
   the lambda names [std::any].  [apply_k] here stands in for [bind]: the
   monad is not the point, being passed as a function is.

   It is not an error site on Vellvm today -- nothing reaches it -- which is
   the worrying reading and not the reassuring one.  It sits directly under
   the [bind]/[ret] calls that are 17 of the 49 named-call failures, all of
   which were byte-identical across the previous fix.  Whether the two are
   connected is untested; fixing this is the discriminator. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class IPtr := { iptr : Set ; zero_iptr : iptr }.

#[global] Instance IPZ : IPtr := { iptr := nat ; zero_iptr := 0 }.

Definition prov : Set := list nat.
Definition nil_prov : prov := nil.

(** Stands in for [EOU_monad]: the callback is handed to a {e dictionary}
    method, not to a plain polymorphic function.  A plain one does not
    reproduce -- see the header. *)
Class Mon (m : Set -> Set) :=
  { ret : forall {A : Set}, A -> m A
  ; bind : forall {A B : Set}, m A -> (A -> m B) -> m B }.

Definition Id (A : Set) : Set := A.
#[global] Instance MonId : Mon Id :=
  { ret := fun A a => a ; bind := fun A B ma k => k ma }.

Class PTR := { ptr : Set ; int_to_ptr : nat -> prov -> Id ptr ; ptr_tag : nat }.

#[global] Instance PointerV {IP : IPtr} : PTR :=
  { ptr := (iptr * prov)%type
  ; int_to_ptr := fun _ pr => bind (ret zero_iptr) (fun x => ret (x, pr))
  ; ptr_tag := 7 }.

Module AssocTypeErasedInLambdaBody.
  Definition go (_ : nat) : nat := @ptr_tag (@PointerV IPZ).
End AssocTypeErasedInLambdaBody.

Crane Extraction "assoc_type_erased_in_lambda_body" AssocTypeErasedInLambdaBody.
