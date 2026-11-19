From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    In a functor, a local fixpoint over [list (st string)] whose accumulator is [sum (option nat) (option string)]: the [None] is built as [optional<crane::obj>] where [optional<unsigned long long>] is expected ("no viable conversion"). *)
Module FunctorStListOptionalObj.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Module Type SIG3.
  Parameter t : Type.
End SIG3.

Module F3 (E : SIG3).
Definition h (a16 : E.t) (a17 : ((st nat) * Z)) : (sum (option nat) (option string)) :=
  (let fix go19 (l20 : (list (st string))) (acc21 : (sum (option nat) (option string))) {struct l20} : (sum (option nat) (option string)) := match l20 with [] => acc21 | e22 :: rest23 => acc21 end in go19 [(sret ""%string)] (@inl (option nat) (option string) (@None nat))).
End F3.
Module M3_1 <: SIG3.
  Definition t : Type := (nat * bool).
End M3_1.
End FunctorStListOptionalObj.

Crane Extraction "functor_st_list_optional_obj" FunctorStListOptionalObj.
