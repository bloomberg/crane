From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
From Crane Require Extraction.

Local Open Scope pstring_scope.
Local Open Scope itree_scope.
Import ITreeNotations.

Set Crane Loopify.

Module CountDown.

Axiom nat_to_string : nat -> string.

(** Single effect then recurse: effect ;; recursive_call *)
Fixpoint count_down (n : nat) : itree ioE unit :=
  match n with
  | O => Ret tt
  | S n' =>
    print_endline "tick" ;;
    count_down n'
  end.

(** Two effects then recurse: effect ;; effect ;; recursive_call *)
Fixpoint two_prints (n : nat) : itree ioE unit :=
  match n with
  | O => Ret tt
  | S n' =>
    print_endline (cat "step " (nat_to_string n)) ;;
    print_endline "---" ;;
    two_prints n'
  end.

(** Read from user, echo back, then recurse *)
Fixpoint echo_loop (n : nat) : itree ioE unit :=
  match n with
  | O => Ret tt
  | S n' =>
    line <- get_line ;;
    print_endline (cat "echo: " line) ;;
    echo_loop n'
  end.

(** Effect in base case too: both branches do IO *)
Fixpoint announce (n : nat) : itree ioE unit :=
  match n with
  | O => print_endline "done"
  | S n' =>
    print_endline (cat "counting " (nat_to_string n)) ;;
    announce n'
  end.

(** Multiple arguments: two nat params, recurse on first *)
Fixpoint repeat_msg (n : nat) (msg : string) : itree ioE unit :=
  match n with
  | O => Ret tt
  | S n' =>
    print_endline msg ;;
    repeat_msg n' msg
  end.

Definition run_fixpoint : itree ioE unit :=
  count_down 3 ;;
  two_prints 3 ;;
  echo_loop 0 ;;
  announce 2 ;;
  repeat_msg 2 "hello".

(** Helper: compare two strings *)
Definition string_eq (s1 s2 : string) : bool :=
  match PrimString.compare s1 s2 with
  | Eq => true
  | _ => false
  end.

(** Coinductive: single effect then Tau-recurse, stop on "stop" *)
CoFixpoint co_count_down : itree ioE unit :=
  line <- get_line ;;
  if string_eq line "stop"
  then Ret tt
  else
    print_endline "tick" ;;
    Tau co_count_down.

(** Coinductive: two effects then Tau-recurse *)
CoFixpoint co_two_prints : itree ioE unit :=
  line <- get_line ;;
  if string_eq line "stop"
  then Ret tt
  else
    print_endline (cat "got: " line) ;;
    print_endline "---" ;;
    Tau co_two_prints.

(** Coinductive: read from user, echo back, then recurse *)
CoFixpoint co_echo_loop : itree ioE unit :=
  line <- get_line ;;
  if string_eq line "quit"
  then Ret tt
  else
    print_endline (cat "echo: " line) ;;
    Tau co_echo_loop.

(** Coinductive: effect in termination branch too *)
CoFixpoint co_announce (round : nat) : itree ioE unit :=
  line <- get_line ;;
  if string_eq line "stop"
  then print_endline "done"
  else
    print_endline (cat "round " (nat_to_string round)) ;;
    Tau (co_announce (S round)).

(** Coinductive: multiple arguments, accumulator pattern *)
CoFixpoint co_repeat (msg : string) : itree ioE unit :=
  line <- get_line ;;
  if string_eq line "stop"
  then Ret tt
  else
    print_endline msg ;;
    Tau (co_repeat msg).

End CountDown.

Crane Extract Inlined Constant CountDown.nat_to_string =>
  "std::to_string(%a0)".

Crane Extract Inlined Constant PrimString.compare =>
  "(%a0 == %a1 ? Comparison::e_EQ : (%a0 < %a1 ? Comparison::e_LT : Comparison::e_GT))".

Crane Extraction "count_down" CountDown.
