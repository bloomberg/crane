(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import String.

Module SimpleIO.

Axiom IO : Type -> Type.
Axiom pure : forall {A}, A -> IO A.
Axiom bind : forall {A B}, IO A -> (A -> IO B) -> IO B.
Axiom get_line : IO string.
Axiom print : string -> IO unit.

Notation "e1 ;; e2" :=
  (@bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).

Definition main : IO unit :=
  print ("Your first name?") ;;
  x <- get_line ;;
  print ("Your last name?") ;;
  y <- get_line ;;
  print ("Hello, " ++ x ++ " " ++ y ++ "!").

End SimpleIO.

Require Crane.Extraction.
Crane Extract Constant SimpleIO.IO "a" => "'a".
Crane Extract Constant SimpleIO.pure => "pure".
Crane Extract Constant SimpleIO.bind => "bind".
Crane Extract Constant SimpleIO.get_line => "get_line".
Crane Extract Constant SimpleIO.print => "print".
Crane Extraction "simple_io" SimpleIO.
