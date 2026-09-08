(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List Arith.
From Crane Require Import Mapping.NatIntStd Mapping.Std.
Import ListNotations.

(** A class method is emitted as a static member function of the instance
    struct, so it has a fixed arity.  Supplying fewer arguments than that -- here
    storing [sz 2] in a list of [nat -> nat] -- is emitted as a call rather than
    eta-expanded into a closure, giving "too few arguments to function call". *)

Module ClassMethodPartialApp.

  Class Sz (A : Type) := { sz : A -> nat -> nat }.

  Instance SzNat : Sz nat := { sz := fun a b => a + b }.

  Definition test : nat :=
    fold_right (fun f n => f 1 + n) 0 [@sz nat _ 2; @sz nat _ 3].

End ClassMethodPartialApp.

Crane Extraction "class_method_partial_app" ClassMethodPartialApp.
