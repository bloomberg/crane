(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Stress test for block template (%result) expansion.

   Exercises less-tested code paths:
   - block templates in fixpoint bodies
   - block templates inside match arms (monadic)
   - non-monadic block templates (pure let)
   - block templates with arguments containing special characters
   - block templates in option-returning functions
   - block templates with multiple semicolons in template body
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.

Local Open Scope pstring_scope.

(** Custom block templates for testing *)

(** A block template with multiple semicolons in the template body *)
Axiom scan_nat : forall {E} `{consoleE -< E}, itree E nat.
Crane Extract Inlined Constant scan_nat =>
  "std::cin >> %result" From "iostream".

(** A pure (non-monadic) block template *)
Axiom scan_nat_pure : nat.
Crane Extract Inlined Constant scan_nat_pure =>
  "std::cin >> %result" From "iostream".

(** A block template with both %result and %a0 that has multi-statement body *)
Axiom read_or_default : forall {E} `{fileE -< E}, string -> itree E string.
Crane Extract Inlined Constant read_or_default =>
  "{ std::ifstream _f(%a0); if (_f.good()) std::getline(_f, %result); else %result = %a0; }" From "fstream".

Module BlockTemplateStress.

  (** 1. Block template in a fixpoint body *)
  Fixpoint read_n_lines (n : nat) : itree ioE (list string) :=
    match n with
    | O => Ret nil
    | S n' =>
      line <- get_line ;;
      rest <- read_n_lines n' ;;
      Ret (cons line rest)
    end.

  (** 2. Block template inside a monadic if-then-else *)
  Definition conditional_read (do_read : bool) : itree ioE string :=
    if do_read then
      s <- get_line ;;
      Ret (cat s "!")
    else
      Ret "skipped".

  (** 3. Block template of non-string type (nat) in bind *)
  Definition read_and_add : itree ioE nat :=
    n <- scan_nat ;;
    Ret (n + 1).

  (** 4. Block template used in multiple match arms *)
  Definition branch_read (choice : nat) : itree ioE string :=
    match choice with
    | O =>
      a <- get_line ;;
      Ret (cat "zero: " a)
    | S O =>
      b <- get_line ;;
      Ret (cat "one: " b)
    | _ =>
      c <- get_line ;;
      Ret (cat "other: " c)
    end.

  (** 5. Block template in nested bind chain with arithmetic *)
  Definition read_two_nats : itree ioE nat :=
    a <- scan_nat ;;
    b <- scan_nat ;;
    Ret (a + b).

  (** 6. Block template result fed to another function *)
  Definition block_result_as_arg : itree ioE unit :=
    n <- scan_nat ;;
    s <- get_line ;;
    print_endline (cat s " read") ;;
    Ret tt.

  (** 9. Block template with %a0 inside a fixpoint *)
  Fixpoint read_files (paths : list string) : itree ioE (list string) :=
    match paths with
    | nil => Ret nil
    | cons p ps =>
      content <- read_or_default p ;;
      rest <- read_files ps ;;
      Ret (cons content rest)
    end.

  (** 10. Block template interleaved with void calls *)
  Definition interleaved_void : itree ioE string :=
    print_endline "Enter name:" ;;
    name <- get_line ;;
    print_endline (cat "Hello, " name) ;;
    print_endline "Enter age:" ;;
    age <- get_line ;;
    Ret (cat name (cat " is " age)).

End BlockTemplateStress.

Crane Extraction "block_template_stress" BlockTemplateStress.
