(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: Dir and Path effects with list matching and bool conditionals.
   Exercises: list_directory IIFE template with list matching,
   bool results from path effects in conditionals, current_path
   (zero-arg effect), and chaining path results into other effects.
*)
From Stdlib Require Import List.
Import ListNotations.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env Monads.Dir Monads.Path.
Local Open Scope pstring_scope.

Module EffectDirPath.

  Definition myE := ioE +' envE +' dirE +' pathE.
  Crane Extract Skip myE.

  (** 1. list_directory result matched — exercises IIFE + list match *)
  Definition first_file (path : string) : itree myE (option string) :=
    files <- list_directory path ;;
    match files with
    | nil => Ret None
    | x :: _ => Ret (Some x)
    end.

  (** 2. current_path (zero args) chained to env *)
  Definition save_cwd : itree myE unit :=
    cwd <- current_path ;;
    set_env "CWD" cwd.

  (** 3. is_directory bool result used in conditional with effects in arms *)
  Definition check_and_list (path : string) : itree myE (option string) :=
    isdir <- is_directory path ;;
    if isdir then
      first_file path
    else
      Ret None.

  (** 4. Path effect result chained to print *)
  Definition show_absolute (path : string) : itree myE unit :=
    abs <- absolute path ;;
    print_endline abs.

  (** 5. Multiple bool effects composed *)
  Definition classify_path (path : string) : itree myE string :=
    isdir <- is_directory path ;;
    isfile <- is_regular_file path ;;
    if isdir then
      Ret "directory"
    else if isfile then
      Ret "file"
    else
      Ret "other".

  (** 6. create_directory bool result explicitly bound and used *)
  Definition create_and_report (path : string) : itree myE string :=
    ok <- create_directory path ;;
    if ok then
      print_endline "Created" ;;
      Ret "created"
    else
      print_endline "Already exists" ;;
      Ret "exists".

  (** 7. Recursive function counting list items from list_directory *)
  Fixpoint count_entries (dirs : list string) (acc : nat)
    : itree myE nat :=
    match dirs with
    | nil => Ret acc
    | d :: rest =>
      files <- list_directory d ;;
      let n := List.length files in
      count_entries rest (acc + n)
    end.

  (** 8. remove_directory (returns bool but treated as unit in bind) *)
  Definition cleanup (path : string) : itree myE unit :=
    _ <- remove_directory path ;;
    print_endline "cleaned up".

End EffectDirPath.

Crane Extraction "effect_dir_path" EffectDirPath.
