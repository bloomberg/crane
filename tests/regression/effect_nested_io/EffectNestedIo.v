(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: nested IO patterns with block templates in complex contexts.
   Exercises block template expansion, recursive monadic functions,
   and interactions between block templates and other effect types.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env Monads.Clock.
Local Open Scope pstring_scope.

Module EffectNestedIo.

  Definition myE := ioE +' envE +' clockE.
  Crane Extract Skip myE.

  (** 1. Block template result used inside constructor (Some) *)
  Definition read_optional : itree myE (option string) :=
    line <- get_line ;;
    Ret (Some line).

  (** 2. Block template result used in a pair *)
  Definition read_pair : itree myE (string * int) :=
    line <- get_line ;;
    let len := PrimString.length line in
    Ret (line, len).

  (** 3. Block template result concatenated with another string *)
  Definition read_and_greet : itree myE string :=
    name <- get_line ;;
    let greeting := cat "Hello, " name in
    Ret greeting.

  (** 4. Two block templates, results used in pair *)
  Definition read_two_lines : itree myE (string * string) :=
    a <- get_line ;;
    b <- get_line ;;
    Ret (a, b).

  (** 5. Block template in function that also uses clock effect *)
  Definition timed_read : itree myE (string * int) :=
    t1 <- steady_now ;;
    line <- get_line ;;
    t2 <- steady_now ;;
    Ret (line, t2).

  (** 6. Block template result stored in env *)
  Definition read_and_store (key : string) : itree myE string :=
    line <- get_line ;;
    set_env key line ;;
    Ret line.

  (** 7. Multiple block templates interleaved with env effects *)
  Definition multi_read_store : itree myE (string * string) :=
    k <- get_line ;;
    set_env "KEY" k ;;
    v <- get_line ;;
    set_env "VALUE" v ;;
    Ret (k, v).

  (** 8. Block template result length checked *)
  Definition read_length : itree myE int :=
    line <- get_line ;;
    Ret (PrimString.length line).

End EffectNestedIo.

Crane Extraction "effect_nested_io" EffectNestedIo.
