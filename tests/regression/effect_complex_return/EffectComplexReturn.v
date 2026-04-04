(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests effect operations with complex return types:
   - pairs, options, lists
   - block templates (get_line) producing values used in structured types
   - void effects interleaved with value-returning effects
   - clock effects returning int used in arithmetic
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env Monads.Clock.
Local Open Scope pstring_scope.

Module EffectComplexReturn.

  Definition myE := ioE +' envE +' clockE.
  Crane Extract Skip myE.

  (** 1. Effect returning a pair *)
  Definition read_pair : itree myE (string * string) :=
    a <- get_line ;;
    b <- get_line ;;
    Ret (a, b).

  (** 2. Effect returning an option *)
  Definition maybe_read (do_read : bool) : itree myE (option string) :=
    if do_read then
      line <- get_line ;;
      Ret (Some line)
    else
      Ret None.

  (** 3. Void effect followed by value effect *)
  Definition print_then_read (prompt : string) : itree myE string :=
    print_endline prompt ;;
    get_line.

  (** 4. Multiple effects with different return types *)
  Definition mixed_effects (name : string) : itree myE (int * string) :=
    t <- now ;;
    mv <- get_env name ;;
    match mv with
    | Some v =>
      print_endline v ;;
      Ret (t, v)
    | None =>
      line <- get_line ;;
      Ret (t, line)
    end.

  (** 5. Clock effect in arithmetic *)
  Definition elapsed_ms : itree myE int :=
    t1 <- steady_now ;;
    t2 <- steady_now ;;
    Ret (sub t2 t1).

  (** 6. Effect result used to build a list *)
  Definition read_n (n : nat) : itree myE (list string) :=
    match n with
    | O => Ret nil
    | S O =>
      x <- get_line ;;
      Ret (cons x nil)
    | S (S O) =>
      x <- get_line ;;
      y <- get_line ;;
      Ret (cons x (cons y nil))
    | _ => Ret nil
    end.

  (** 7. Env effect result used in conditional *)
  Definition env_or_prompt (name : string) : itree myE string :=
    mv <- get_env name ;;
    match mv with
    | Some v => Ret v
    | None =>
      print_endline (cat "Enter " (cat name ":")) ;;
      get_line
    end.

End EffectComplexReturn.

Crane Extraction "effect_complex_return" EffectComplexReturn.
