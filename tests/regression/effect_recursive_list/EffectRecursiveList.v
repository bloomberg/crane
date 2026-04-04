(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: recursive monadic functions building data structures from effects.
   Exercises: fixpoint + bind interaction, block template in recursive context,
   constructor calls after effects, higher-order effect callbacks.
*)
From Stdlib Require Import List.
Import ListNotations.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectRecursiveList.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Recursive function building a list from stdin lines *)
  Fixpoint read_n_lines (n : nat) : itree myE (list string) :=
    match n with
    | O => Ret nil
    | S n' =>
      line <- get_line ;;
      rest <- read_n_lines n' ;;
      Ret (line :: rest)
    end.

  (** 2. Map a function over a list with effects *)
  Fixpoint map_effect (f : string -> itree myE unit) (xs : list string)
    : itree myE unit :=
    match xs with
    | nil => Ret tt
    | x :: xs' =>
      f x ;;
      map_effect f xs'
    end.

  (** 3. Fold a list with effects, accumulating a result *)
  Fixpoint fold_effect (xs : list string) (acc : string)
    : itree myE string :=
    match xs with
    | nil => Ret acc
    | x :: xs' =>
      print_endline x ;;
      fold_effect xs' (cat acc (cat " " x))
    end.

  (** 4. Read lines and store each in env with index *)
  Fixpoint store_lines (prefix : string) (n : nat)
    : itree myE nat :=
    match n with
    | O => Ret O
    | S n' =>
      line <- get_line ;;
      set_env prefix line ;;
      rest <- store_lines prefix n' ;;
      Ret (S rest)
    end.

  (** 5. Collect env values into a list *)
  Fixpoint collect_envs (names : list string)
    : itree myE (list (option string)) :=
    match names with
    | nil => Ret nil
    | name :: rest =>
      val <- get_env name ;;
      vals <- collect_envs rest ;;
      Ret (val :: vals)
    end.

  (** 6. Read a line and prepend to existing list *)
  Definition read_and_prepend (xs : list string) : itree myE (list string) :=
    line <- get_line ;;
    Ret (line :: xs).

End EffectRecursiveList.

Crane Extraction "effect_recursive_list" EffectRecursiveList.
