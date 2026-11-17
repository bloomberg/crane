From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A local fixpoint that calls itself at [bool], not at the [list nat] it
    is entered at: polymorphic recursion.  Extraction types a local
    fixpoint's body at one instance, which the call at [bool] would pin, so
    the entry's list would reach a [bool] loop variable.  Instead the
    fixpoint's type binder is erased ([Extraction.erased_fix_types]): [y] is
    a [crane::obj], [h] a [crane::fn<uint64_t(crane::obj)>], and each closure
    stored into [h] goes through [crane_erase_fn].  The top-level [Fixpoint]
    is [self_call_other_instance]. *)

Module LocalFixPolymorphicRecursion.

  Definition run (k : nat) (n : nat) : nat :=
    let fix f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
      match n with
      | O => h y
      | S m => f bool (fun b => if b then 10 + k else 20) true m
      end
    in f (list nat) (@length nat) [1; 2; 3] n.

End LocalFixPolymorphicRecursion.

Crane Extraction "local_fix_polymorphic_recursion" LocalFixPolymorphicRecursion.
