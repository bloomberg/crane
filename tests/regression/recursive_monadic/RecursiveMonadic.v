(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Recursive monadic functions returning non-void.
    Tests recursion in sequential ITree mode with value-returning functions. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module RecursiveMonadic.

(** 1. Simple recursive countdown with effect *)
Fixpoint countdown (n : nat) : itree ioE nat :=
  match n with
  | O => Ret 0
  | S n' => print_endline "tick" ;; countdown n'
  end.

(** 2. Recursive sum over list with logging *)
Fixpoint sum_list (xs : list nat) : itree ioE nat :=
  match xs with
  | nil => Ret 0
  | cons x rest =>
    print_endline "adding" ;;
    s <- sum_list rest ;;
    Ret (x + s)
  end.

(** 3. Recursive collect: transforms each element with effect *)
Fixpoint collect_lengths (xs : list string) : itree ioE (list int) :=
  match xs with
  | nil => Ret nil
  | cons s rest =>
    print_endline s ;;
    rest' <- collect_lengths rest ;;
    Ret (cons (PrimString.length s) rest')
  end.

(** 4. Recursive with two recursive calls (tree-like) *)
Fixpoint repeat_action (n : nat) (msg : string) : itree ioE nat :=
  match n with
  | O => Ret 0
  | S n' =>
    print_endline msg ;;
    r <- repeat_action n' msg ;;
    Ret (S r)
  end.

(** 5. Recursive with match in the middle *)
Fixpoint filter_print (pred : nat -> bool) (xs : list nat) : itree ioE (list nat) :=
  match xs with
  | nil => Ret nil
  | cons x rest =>
    rest' <- filter_print pred rest ;;
    if pred x
    then (print_endline "keep" ;; Ret (cons x rest'))
    else Ret rest'
  end.

(** 6. Recursive with block template in each step *)
Fixpoint read_n_lines (n : nat) : itree ioE (list string) :=
  match n with
  | O => Ret nil
  | S n' =>
    line <- get_line ;;
    rest <- read_n_lines n' ;;
    Ret (cons line rest)
  end.

(** 7. Mutual-like: two functions calling each other via wrapper *)
Fixpoint even_action (n : nat) : itree ioE string :=
  match n with
  | O => Ret "even"
  | S n' => print_endline "e" ;; odd_action n'
  end
with odd_action (n : nat) : itree ioE string :=
  match n with
  | O => Ret "odd"
  | S n' => print_endline "o" ;; even_action n'
  end.

(** 8. Recursive option-returning function *)
Fixpoint find_first (pred : nat -> bool) (xs : list nat) : itree ioE (option nat) :=
  match xs with
  | nil => Ret None
  | cons x rest =>
    print_endline "checking" ;;
    if pred x then Ret (Some x)
    else find_first pred rest
  end.

End RecursiveMonadic.

Crane Extraction "recursive_monadic" RecursiveMonadic.
