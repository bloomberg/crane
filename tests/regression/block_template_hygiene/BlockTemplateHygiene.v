(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test for block template (%result) hygiene.

   Tests that %result expansion in multi-statement inline customs does not
   cause variable shadowing, name collisions, or scoping errors when:
   - the same bind name is reused multiple times
   - the bind name collides with names inside the template body
   - multiple block templates appear in the same scope
   - block templates carry %a0/%a1 arguments alongside %result
   - block templates appear inside let-bindings (not just monadic bind)
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

(** A custom block template with both %result and %a0. *)
Axiom read_trimmed : forall {E} `{fileE -< E}, string -> itree E string.
Crane Extract Inlined Constant read_trimmed =>
  "{ std::ifstream _f(%a0); std::getline(_f, %result); }" From "fstream".

Module BlockTemplateHygiene.

  (** Test 1: Two consecutive get_line calls with the SAME binder name [s].
      The second [s] should be freshened (e.g., s0) by Crane's rename_id. *)
  Definition same_name_twice : itree ioE string :=
    s <- get_line ;;
    s <- get_line ;;
    Ret (cat s " (second)").

  (** Test 2: Three consecutive get_line calls, all named [s].
      Tests multiple rounds of freshening. *)
  Definition same_name_thrice : itree ioE string :=
    s <- get_line ;;
    s <- get_line ;;
    s <- get_line ;;
    Ret (cat s " (third)").

  (** Test 3: get_line with bind name [s] — the exact variable name that the old
      IIFE template used internally ([std::string s; std::getline(std::cin, s)]).
      With block templates, there is no internal variable; %result IS the
      bind target, so no collision.
      Note: we use [cat s "!"] instead of [Ret s] to prevent the monad right
      identity optimization ([bind m Ret = m]) from bypassing the bind handler. *)
  Definition shadow_internal_name : itree ioE string :=
    s <- get_line ;;
    Ret (cat s "!").

  (** Test 4: Multiple different block templates in the same scope.
      Uses get_line (block template) interleaved with print (expression template)
      to verify that block templates don't interfere with expression templates. *)
  Definition interleaved_templates : itree ioE string :=
    a <- get_line ;;
    print a ;;
    b <- get_line ;;
    print_endline b ;;
    c <- get_line ;;
    Ret (cat a (cat b c)).

  (** Test 5: Block template with %a0 argument alongside %result.
      Uses our custom [read_trimmed] which has both %result and %a0. *)
  Definition block_with_args : itree ioE string :=
    s <- read_trimmed "data.txt" ;;
    Ret (cat s " read").

  (** Test 6: Multiple block templates with %a0, same binder name.
      Two calls to [read_trimmed] both named [s]. *)
  Definition block_with_args_same_name : itree ioE string :=
    s <- read_trimmed "a.txt" ;;
    s <- read_trimmed "b.txt" ;;
    Ret (cat s " done").

  (** Test 7: Block template result used as an argument to another call.
      Tests that the generated variable is properly referenced after the
      block expansion. *)
  Definition result_in_expr : itree ioE unit :=
    name <- get_line ;;
    print_endline (cat "Hello, " name) ;;
    Ret tt.

  (** Test 8: Block template in a let-binding context (non-monadic).
      Uses a let to capture an intermediate value derived from a block
      template result. *)
  Definition let_after_block : itree ioE string :=
    first <- get_line ;;
    last <- get_line ;;
    let full := cat first (cat " " last) in
    Ret full.

  (** Test 9: get_line bound to the name [result] to stress-test that
      the C++ variable [result] doesn't collide with any internal
      expansion logic. *)
  Definition bind_named_result : itree ioE string :=
    result <- get_line ;;
    Ret (cat result "!").

  (** Test 10: get_line bound to the name [_r] — the internal IIFE
      fallback variable name. Ensures no collision with the expression-
      position IIFE wrapper's internal variable. *)
  Definition bind_named_underscore_r : itree ioE string :=
    _r <- get_line ;;
    Ret (cat _r "!").

  (** Test 11: Block template in pure expression position (not in bind).
      Verifies that the IIFE fallback generates valid C++ when a block
      template is used as a subexpression.
      [bind get_line Ret] triggers the monad right identity optimization,
      placing get_line directly in expression position. *)
  Definition expr_position_iife : itree ioE string :=
    s <- get_line ;;
    Ret s.

End BlockTemplateHygiene.

Crane Extraction "block_template_hygiene" BlockTemplateHygiene.
