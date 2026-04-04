(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Workflow test: combines multiple effect types in complex patterns.
   Exercises: block templates, option matching, bool matching,
   effects inside match arms, recursive monadic functions,
   and functions returning complex types from effects.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env Monads.Dir Monads.Clock Monads.TempFile.
Local Open Scope pstring_scope.

Module EffectWorkflow.

  Definition allE := ioE +' envE +' dirE +' clockE +' tempFileE.
  Crane Extract Skip allE.

  (** 1. Use 5 different effect types in one function *)
  Definition full_workflow (prefix : string) : itree allE string :=
    t1 <- steady_now ;;
    tmp <- create_temp_file prefix ;;
    ok <- create_directory tmp ;;
    set_env "LAST_TEMP" tmp ;;
    print_endline tmp ;;
    t2 <- steady_now ;;
    Ret tmp.

  (** 2. Match on bool from create_directory inside a chain *)
  Definition conditional_create (path : string) : itree allE string :=
    ok <- create_directory path ;;
    if ok then
      print_endline "created" ;;
      Ret path
    else
      Ret "exists".

  (** 3. get_line (block template) followed by env set using the result *)
  Definition read_and_set : itree allE unit :=
    line <- get_line ;;
    set_env "USER_INPUT" line.

  (** 4. Recursive function using effects *)
  Fixpoint repeat_log (n : nat) (msg : string) : itree allE nat :=
    match n with
    | O => Ret 0
    | S n' =>
      t <- steady_now ;;
      print_endline msg ;;
      r <- repeat_log n' msg ;;
      Ret (S r)
    end.

  (** 5. Effect returning option, matched, then another effect *)
  Definition env_or_create (name path : string) : itree allE string :=
    r <- get_env name ;;
    match r with
    | Some v => Ret v
    | None =>
      ok <- create_directory path ;;
      set_env name path ;;
      Ret path
    end.

  (** 6. Pure let after block template *)
  Definition read_length : itree allE int :=
    line <- get_line ;;
    let len := PrimString.length line in
    Ret len.

  (** 7. Multiple block templates of different types *)
  Definition double_read : itree allE (string * string) :=
    a <- get_line ;;
    b <- get_line ;;
    Ret (a, b).

  (** 8. Return int literal in monadic context *)
  Definition return_literal : itree allE int :=
    Ret 42%int63.

End EffectWorkflow.

Crane Extraction "effect_workflow" EffectWorkflow.
