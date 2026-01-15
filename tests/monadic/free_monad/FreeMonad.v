(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import PrimString.

Module FreeMonad.

Inductive IO : Type -> Type :=
| pure : forall {A}, A -> IO A
| bind : forall {A B}, IO A -> (A -> IO B) -> IO B
| get_line : IO string
| print : string -> IO unit.

Notation "e1 ;; e2" :=
  (@bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).

Definition test : IO unit := pure tt.

(*
  print ("Your first name?") ;;
  x <- get_line ;;
  print ("Your last name?") ;;
  y <- get_line ;;
  print ("Hello, " ++ x ++ " " ++ y ++ "!"). *)

(*

IO_rect =
fun (P : forall T : Type, IO T -> Type)
  (f : forall (A : Type) (a : A), P A (pure a))
  (f0 : forall (A B : Type) (i : IO A),
	    P A i ->
        forall i0 : A -> IO B,
        (forall a : A, P B (i0 a)) -> P B (x <- i;; i0 x))
  (f1 : P string get_line) (f2 : forall s : string, P unit (print s)) =>
fix F (T : Type) (i : IO T) {struct i} : P T i :=
  match i as i0 in (IO T0) return (P T0 i0) with
  | @pure A a => f A a
  | @bind A B i0 i1 => f0 A B i0 (F A i0) i1 (fun a : A => F B (i1 a))
  | get_line => f1
  | print s => f2 s
  end
     : forall P : forall T : Type, IO T -> Type,
       (forall (A : Type) (a : A), P A (pure a)) ->
       (forall (A B : Type) (i : IO A),
        P A i ->
        forall i0 : A -> IO B,
        (forall a : A, P B (i0 a)) -> P B (x <- i;; i0 x)) ->
       P string get_line ->
       (forall s : string, P unit (print s)) ->
       forall (T : Type) (i : IO T), P T i

IO_rec =
fun P : forall T : Type, IO T -> Set => IO_rect P
	 : forall P : forall T : Type, IO T -> Set,
       (forall (A : Type) (a : A), P A (pure a)) ->
       (forall (A B : Type) (i : IO A),
        P A i ->
        forall i0 : A -> IO B,
        (forall a : A, P B (i0 a)) -> P B (x <- i;; i0 x)) ->
       P string get_line ->
       (forall s : string, P unit (print s)) ->
       forall (T : Type) (i : IO T), P T i
*)

End FreeMonad.

Require Crane.Extraction.
Crane Extract Inlined Constant string => "std::string" From "string".
Crane Extraction TestCompile "free_monad" FreeMonad.
