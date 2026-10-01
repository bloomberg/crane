(* A class's [Type] field, used as a type outside any instance struct, is
   spelled unqualified even where the instance is named in the very term that
   inhabits it.

     using ptr = std::any;                                    // file scope
     ...
     static inline const EOU<ptr> run = PIV<natIPtr>::int_to_ptr(...);

   [run]'s initialiser says [PIV<natIPtr>], whose own [using ptr] is
   [std::pair<typename _tcI0::iptr, typename _tcI0::prov>], so the qualifier
   is present in the term and dropped from the type.  Inside the instance
   struct the same field resolves correctly -- that is the [Tpromoted]
   resolution map -- and outside it falls back to a file-scope [using] of the
   same name, which is the erased spelling.

   The file-scope alias is not itself the defect.  It is what a use with no
   instance in sight must resolve to, and there are such uses; the defect is
   that a use with an instance in sight resolves to it anyway.

   Fixed: the resolution is taken from the term.  The type records [ptr]
   applied to no arguments at all -- extraction keeps no trace of the instance
   there -- but the body is a projection whose scrutinee names it, and the C++
   type of that scrutinee is the one the emitted call already uses, so the
   declaration and its initialiser agree by construction:

     static inline const EOU<typename PIV<natIPtr>::ptr> run = PIV<natIPtr>::...

   This lands on any consumer of a method whose result mentions a class field,
   which is why instance_method_param_at_foreign_class_field -- the same class
   shapes, fixed in b776fe215 -- deliberately returns [EOU nat] instead.  The
   two are otherwise the same reduction.

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
  {| ret  := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Class IPtr := { iptr : Type ; prov : Type ; from_Z : nat -> EOU iptr }.

Class ITOP (P : IPtr) := { ptr : Type ; int_to_ptr : nat -> @prov P -> EOU ptr }.

#[global] Instance PIV {IP : IPtr} : ITOP IP :=
  {| ptr := (iptr * prov)%type
   ; int_to_ptr := fun i pr => bind (from_Z i) (fun a => ret (a, pr)) |}.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; prov := bool ; from_Z := fun n => ret n |}.

Module InstanceCarrierUnqualifiedAtKnownInstance.
  Definition run := @int_to_ptr natIPtr (@PIV natIPtr) 1 true.
End InstanceCarrierUnqualifiedAtKnownInstance.

Set Crane Format Style "None".
Crane Extraction "instance_carrier_unqualified_at_known_instance" InstanceCarrierUnqualifiedAtKnownInstance.
