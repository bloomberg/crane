(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests effects that return list and other compound types.
   Exercises the interaction between effect erasure and complex
   type construction.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Dir Monads.Clock.
Local Open Scope pstring_scope.

Module EffectListReturn.

  Definition myE := ioE +' dirE +' clockE.
  Crane Extract Skip myE.

  (** 1. list_directory returns a list *)
  Definition list_files (path : string) : itree myE (list string) :=
    list_directory path.

  (** 2. create dir and verify *)
  Definition make_and_check (path : string) : itree myE bool :=
    ok <- create_directory path ;;
    Ret ok.

  (** 3. get_time result used in pair *)
  Definition timestamped_line : itree myE (int * string) :=
    t <- now ;;
    line <- get_line ;;
    Ret (t, line).

  (** 4. current_path as a no-arg effect *)
  Definition get_cwd : itree myE string :=
    current_path.

  (** 5. Chain effects with different return types *)
  Definition create_and_list (dir : string) : itree myE (bool * list string) :=
    ok <- create_directory dir ;;
    if ok then
      files <- list_directory dir ;;
      Ret (true, files)
    else
      Ret (false, nil).

End EffectListReturn.

Crane Extraction "effect_list_return" EffectListReturn.
