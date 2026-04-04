(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Stress test for get_line (block template with %result) in
   various contexts: match arms, fixpoints, let-chains, if-then-else,
   and nested binds.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module EffectGetlineStress.

(** 1. get_line in both branches of if-then-else *)
Definition get_or_default (ask : bool) : itree ioE string :=
  if ask
  then get_line
  else Ret "default".

(** 2. get_line in a match arm *)
Definition get_nth_line (n : nat) : itree ioE string :=
  match n with
  | O => Ret "none"
  | S O => get_line
  | S (S _) =>
    _ <- get_line ;;
    get_line
  end.

(** 3. Recursive function that uses get_line in a loop *)
Fixpoint read_lines (n : nat) (acc : list string) : itree ioE (list string) :=
  match n with
  | O => Ret acc
  | S n' =>
    line <- get_line ;;
    read_lines n' (cons line acc)
  end.

(** 4. get_line result immediately used in another effect *)
Definition read_and_echo : itree ioE unit :=
  line <- get_line ;;
  print_endline line.

(** 5. get_line result used in a let chain *)
Definition get_line_length : itree ioE int :=
  line <- get_line ;;
  let len := PrimString.length line in
  Ret len.

(** 6. Two get_lines with results combined *)
Definition concat_two_lines : itree ioE string :=
  a <- get_line ;;
  b <- get_line ;;
  Ret (PrimString.cat a b).

(** 7. get_line inside a monadic map *)
Definition get_and_measure : itree ioE (string * int) :=
  line <- get_line ;;
  let len := PrimString.length line in
  Ret (line, len).

(** 8. Conditional get_line with print *)
Definition interactive_prompt (ask : bool) : itree ioE string :=
  if ask then
    print_endline "Enter input:" ;;
    line <- get_line ;;
    print_endline "Got it" ;;
    Ret line
  else
    Ret "skipped".

End EffectGetlineStress.

Crane Extraction "effect_getline_stress" EffectGetlineStress.
