(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for unit→void in monadic/itree context.
    Tests interactions between bind, effects, and unit return types. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.

Module MonadicVoidEdge.

(** 1. Bind where LHS is void and RHS returns a value *)
Definition bind_void_then_value : itree ioE nat :=
  print_endline "hello" ;; Ret 42.

(** 2. Bind where both sides are void *)
Definition bind_void_void : itree ioE unit :=
  print_endline "a" ;; print_endline "b" ;; Ret tt.

(** 3. Let-binding the result of a monadic void call *)
Definition let_bind_monadic_void : itree ioE nat :=
  x <- (print_endline "side effect" ;; Ret tt) ;;
  Ret 99.

(** 4. Passing unit through a chain of binds *)
Definition unit_chain : itree ioE unit :=
  x <- Ret tt ;;
  y <- Ret x ;;
  Ret y.

(** 5. Match on a value obtained from a bind *)
Definition match_after_bind : itree ioE nat :=
  b <- Ret true ;;
  Ret (if b then 1 else 0).

(** 6. Void function called in a non-tail bind position *)
Definition void_nontail : itree ioE string :=
  print_endline "prefix" ;;
  name <- get_line ;;
  print_endline name ;;
  Ret name.

(** 7. Nested binds returning unit at every level *)
Definition deeply_nested_void : itree ioE unit :=
  print_endline "1" ;;
  print_endline "2" ;;
  print_endline "3" ;;
  print_endline "4" ;;
  Ret tt.

(** 8. Higher-order: pass a monadic void function as callback *)
Definition apply_effect (f : nat -> itree ioE unit) (n : nat) : itree ioE unit :=
  f n.

Definition test_apply_effect : itree ioE unit :=
  apply_effect (fun n => print_endline "applied") 5.

(** 9. Monadic function returning option unit *)
Definition maybe_print (b : bool) : itree ioE (option unit) :=
  if b then
    print_endline "yes" ;; Ret (Some tt)
  else
    Ret None.

(** 10. Bind result used in a pair *)
Definition bind_into_pair : itree ioE (nat * nat) :=
  a <- Ret 1 ;;
  b <- Ret 2 ;;
  Ret (a, b).

(** 11. Void function result stored in list (should stay Unit, not void) *)
Definition unit_in_list : itree ioE (list unit) :=
  x <- Ret tt ;;
  y <- Ret tt ;;
  Ret (cons x (cons y nil)).

(** 12. Mixed: some binds void, some value, interleaved *)
Definition mixed_binds : itree ioE nat :=
  print_endline "start" ;;
  a <- Ret 10 ;;
  print_endline "middle" ;;
  b <- Ret 20 ;;
  print_endline "end" ;;
  Ret (a + b).

(** 13. Function that takes itree as argument and sequences *)
Definition sequence_effects (e1 e2 : itree ioE unit) : itree ioE unit :=
  e1 ;; e2.

Definition test_sequence : itree ioE unit :=
  sequence_effects (print_endline "first") (print_endline "second").

End MonadicVoidEdge.

Crane Extraction "monadic_void_edge" MonadicVoidEdge.
