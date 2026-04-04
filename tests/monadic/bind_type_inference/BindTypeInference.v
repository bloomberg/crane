(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test cases for bind where return type B has metas independent of parameter type A *)

From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Monads.ITree Monads.IO External.Vector.

Module BindTypeInference.

  Open Scope int63.

  (* Case 1: Parameter is unit, return type has type variable *)
  (* bind : IO unit -> (unit -> IO B) -> IO B *)
  (* Here A=unit (no metas), B=list int (concrete but through a polymorphic path) *)
  Definition ignoreAndReturn {B : Type} (b : B) : itree ioE B :=
    _ <- Ret tt ;;
    Ret b.

  Definition test1 : itree ioE int :=
    ignoreAndReturn 42.

  (* Case 2: More complex - parameter and return have different type variables *)
  (* This tests if B's metas get resolved when A's metas are unrelated *)
  Definition transform {A B : Type} (ma : itree ioE A) (f : A -> B) : itree ioE B :=
    x <- ma ;;
    Ret (f x).

  Definition test2 : itree ioE int :=
    transform (Ret tt) (fun _ => 42).

  (* Case 3: Nested binds with different type variables *)
  Definition nested {A B C : Type} (a : A) (f : A -> B) (g : B -> C) : itree ioE C :=
    x <- Ret a ;;
    y <- Ret (f x) ;;
    Ret (g y).

  Definition test3 : itree ioE int :=
    nested tt (fun _ => true) (fun b => if b then 1 else 0).

  (* Case 4: Vector operations returning different type *)
  Definition test4 : itree vectorE int :=
    v <- emptyVec int ;;
    push v 1 ;;
    push v 2 ;;
    push v 3 ;;
    size v.  (* Returns IO int, not IO (vector int) *)

  (* Case 5: Return type B is a completely different polymorphic type *)
  (* Here A = int, B = list int - testing if list's type param resolves *)
  Definition intToList (n : int) : list int := cons n nil.

  Definition test5 : itree ioE (list int) :=
    x <- Ret (1 : int) ;;
    Ret (intToList x).

  (* Case 6: Direct nested bind - no separate function *)
  Definition test6 : itree ioE int :=
    x <- Ret tt ;;
    y <- Ret true ;;
    Ret (if y then 42 else 0).

End BindTypeInference.

Crane Extraction "bind_type_inference" BindTypeInference.
