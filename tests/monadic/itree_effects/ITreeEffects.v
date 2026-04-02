(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: Effect composition using the real InteractionTrees library.

   Demonstrates multiple effect types defined as inductives, composed
   with [+'], and lifted via [embed].
*)
From Corelib Require Import PrimString.
Require Import Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree.

(** ------------------------------------------------------------------ *)
(** Effect types                                                        *)
(** ------------------------------------------------------------------ *)

Inductive consoleE : Type -> Type :=
| PrintEndline : string -> consoleE unit
| GetLine : consoleE string.

Inductive randomE : Type -> Type :=
| RandomNat : nat -> randomE nat.

Inductive timeE : Type -> Type :=
| GetTime : timeE nat.

Crane Extract Skip consoleE.
Crane Extract Skip randomE.
Crane Extract Skip timeE.

(** ------------------------------------------------------------------ *)
(** Combined effect type                                                *)
(** ------------------------------------------------------------------ *)

Definition appE := consoleE +' randomE +' timeE.
Crane Extract Skip appE.

(** ------------------------------------------------------------------ *)
(** Smart constructors via [embed]                                      *)
(** ------------------------------------------------------------------ *)

Definition print_endline (s : string) : itree appE unit := embed (PrintEndline s).
Definition get_line : itree appE string := embed GetLine.
Definition random_nat (bound : nat) : itree appE nat := embed (RandomNat bound).
Definition get_time : itree appE nat := embed GetTime.

(** ------------------------------------------------------------------ *)
(** Extraction mappings                                                 *)
(** ------------------------------------------------------------------ *)

Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'" From "iostream".
Crane Extract Inlined Constant get_line =>
  "std::getline(std::cin, %result)" From "iostream".
Crane Extract Inlined Constant random_nat => "(std::rand() % %a0)" From "cstdlib".
Crane Extract Inlined Constant get_time =>
  "static_cast<unsigned int>(std::time(nullptr))" From "ctime".

(** ------------------------------------------------------------------ *)
(** Test programs                                                       *)
(** ------------------------------------------------------------------ *)

Module ITreeEffects.

Definition greet : itree appE unit :=
  print_endline "What is your name?" ;;
  name <- get_line ;;
  print_endline name ;;
  Ret tt.

Definition roll_dice (sides : nat) : itree appE nat :=
  n <- random_nat sides ;;
  Ret (n + 1).

Definition timed_greeting : itree appE unit :=
  t <- get_time ;;
  print_endline (if Nat.leb t 43200 then "Good morning" else "Good afternoon") ;;
  Ret tt.

Definition echo_loop (n : nat) : itree appE unit :=
  Nat.iter n (fun acc =>
    line <- get_line ;;
    print_endline line ;;
    acc) (Ret tt).

End ITreeEffects.

Crane Extraction "itree_effects" ITreeEffects.
