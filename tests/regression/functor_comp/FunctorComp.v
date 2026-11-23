(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Module functors, signatures, composition. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module FunctorComp.

(* Module type: a container with an element type and ops *)
Module Type CONTAINER.
  Parameter t : Type.
  Parameter empty : t.
  Parameter push : nat -> t -> t.
  Parameter pop : t -> option (nat * t).
  Parameter size : t -> nat.
End CONTAINER.

(* Stack implementation *)
Module Stack <: CONTAINER.
  Definition t := list nat.
  Definition empty : t := nil.
  Definition push (x : nat) (s : t) : t := x :: s.
  Definition pop (s : t) : option (nat * t) :=
    match s with
    | nil => None
    | x :: rest => Some (x, rest)
    end.
  Definition size (s : t) : nat := length s.
End Stack.

(* Queue implementation (naive: two lists) *)
Module Queue <: CONTAINER.
  Definition t := (list nat * list nat)%type.
  Definition empty : t := (nil, nil).
  Definition push (x : nat) (q : t) : t :=
    let '(front, back) := q in (front, x :: back).
  Definition pop (q : t) : option (nat * t) :=
    let '(front, back) := q in
    match front with
    | x :: rest => Some (x, (rest, back))
    | nil =>
        match rev back with
        | nil => None
        | x :: rest => Some (x, (rest, nil))
        end
    end.
  Definition size (q : t) : nat :=
    let '(front, back) := q in length front + length back.
End Queue.

(* Functor: operations generic over any CONTAINER *)
Module ContainerOps (C : CONTAINER).
  Definition push_list (l : list nat) (c : C.t) : C.t :=
    fold_left (fun acc x => C.push x acc) l c.

  Definition to_list (c : C.t) : list nat :=
    let fix go (fuel : nat) (acc : list nat) (c : C.t) :=
      match fuel with
      | 0 => rev acc
      | S f =>
          match C.pop c with
          | None => rev acc
          | Some (x, c') => go f (x :: acc) c'
          end
      end
    in go (C.size c) nil c.
End ContainerOps.

(* Instantiate functor *)
Module StackOps := ContainerOps Stack.
Module QueueOps := ContainerOps Queue.

(* Test values *)
Definition test_stack : list nat :=
  StackOps.to_list (StackOps.push_list [1; 2; 3] Stack.empty).

Definition test_queue : list nat :=
  QueueOps.to_list (QueueOps.push_list [1; 2; 3] Queue.empty).

Definition test_stack_size : nat :=
  Stack.size (StackOps.push_list [10; 20; 30] Stack.empty).

Definition test_queue_size : nat :=
  Queue.size (QueueOps.push_list [10; 20; 30] Queue.empty).

End FunctorComp.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "functor_comp" FunctorComp.
