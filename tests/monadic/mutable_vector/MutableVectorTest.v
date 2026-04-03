(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Monads.ITree Monads.IO.
From Crane Require Import External.Vector.

Module MutableVectorTest.

  Open Scope int63.

    Definition test1 (x : int) : itree ioE int :=
    v <- emptyVec int ;;
    push v 3 ;;
    push v 2 ;;
    push v 7 ;;
    x <- size v ;;
    pop v ;;
    y <- size v ;;
    Ret (sub x y).

  Definition test2 (x : int) : itree ioE (vector int) :=
    v <- emptyVec int ;;
    push v 12 ;;
    push v 23 ;;
    pop v ;;
    push v 3 ;;
    x <- size v ;;
    push v x ;;
    y <- get v 2 ;;
    push v 98 ;;
    push v y ;;
    Ret v.

End MutableVectorTest.

Crane Extraction "mutable_vector" MutableVectorTest.
