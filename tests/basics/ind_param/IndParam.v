(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Test: Functor taking a module that provides an inductive type *)

From Stdlib Require Import NArith.
Open Scope nat_scope.

(* Module type requiring an inductive with specific structure *)
Module Type Container.
  Parameter elem : Type.

  (* The module must provide an inductive container type *)
  Inductive t : Type :=
  | Empty : t
  | Single : elem -> t
  | Pair : elem -> elem -> t.

  Parameter size : t -> nat.
End Container.

(* Functor that wraps a container with additional operations *)
Module Wrapper (C : Container).
  (* Use the container's type *)
  Definition wrapped := C.t.

  (* Inductive for operation results *)
  Inductive result : Type :=
  | Ok : C.t -> result
  | Err : nat -> result.

  (* Functions using both inductives *)
  Definition make_single (e : C.elem) : result :=
    Ok (C.Single e).

  Definition make_pair (e1 e2 : C.elem) : result :=
    Ok (C.Pair e1 e2).

  Definition get_size (r : result) : nat :=
    match r with
    | Ok c => C.size c
    | Err code => 0
    end.

  (* Example values *)
  Definition empty_result : result := Ok C.Empty.
  Definition error_result : result := Err 404.
End Wrapper.

(* Concrete container implementation *)
Module NatContainer <: Container.
  Definition elem := nat.

  Inductive t : Type :=
  | Empty : t
  | Single : elem -> t
  | Pair : elem -> elem -> t.

  Definition size (c : t) : nat :=
    match c with
    | Empty => 0
    | Single _ => 1
    | Pair _ _ => 2
    end.
End NatContainer.

(* Instantiate the wrapper *)
Module NatWrapper := Wrapper NatContainer.

(* Test values *)
Definition test_single := NatWrapper.make_single 42.
Definition test_pair := NatWrapper.make_pair 1 2.
Definition test_size_single := NatWrapper.get_size test_single.
Definition test_size_pair := NatWrapper.get_size test_pair.
Definition test_error := NatWrapper.get_size NatWrapper.error_result.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction "ind_param" test_size_single test_size_pair test_error.
