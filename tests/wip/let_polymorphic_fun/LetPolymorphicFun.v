From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A [let]-bound function that takes a type argument becomes one monomorphic
    C++ lambda, [_anon_f], whose parameter types are fixed by whichever use
    site was translated first.  The other two uses then have no matching
    overload. *)

Module LetPolymorphicFun.

  Definition run : nat :=
    let f := fun (A : Type) (x : A) (l : list A) => List.length (x :: l) in
    f nat 1 [2;3] + f bool true [] + f (nat -> nat) S [].

End LetPolymorphicFun.

Crane Extraction "let_polymorphic_fun" LetPolymorphicFun.
