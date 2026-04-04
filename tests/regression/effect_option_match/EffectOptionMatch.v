(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests effect operations that return option types, combined with
   pattern matching on the result.  Targets the interaction between
   bind desugaring, match codegen, and option type handling.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectOptionMatch.

(** Combined effect: IO + Env *)
Definition myE := ioE +' envE.
Crane Extract Skip myE.

(** 1. get_env returns option, match immediately *)
Definition show_or_default (name default : string) : itree myE string :=
  mv <- get_env name ;;
  match mv with
  | Some v => Ret v
  | None => Ret default
  end.

(** 2. get_env with effect in one branch *)
Definition show_or_ask (name : string) : itree myE string :=
  mv <- get_env name ;;
  match mv with
  | Some v => Ret v
  | None =>
    print_endline "Not set, enter value:" ;;
    get_line
  end.

(** 3. Multiple option matches in sequence *)
Definition get_first_set (names : list string) : itree myE string :=
  match names with
  | nil => Ret "none"
  | cons n rest =>
    mv <- get_env n ;;
    match mv with
    | Some v => Ret v
    | None =>
      match rest with
      | nil => Ret "none"
      | cons n2 _ =>
        mv2 <- get_env n2 ;;
        match mv2 with
        | Some v2 => Ret v2
        | None => Ret "none"
        end
      end
    end
  end.

(** 4. set then get, match on result *)
Definition set_and_verify (name value : string) : itree myE bool :=
  set_env name value ;;
  mv <- get_env name ;;
  match mv with
  | Some v =>
    Ret true
  | None => Ret false
  end.

(** 5. Recursive function with option matching *)
Fixpoint find_env_value (names : list string) : itree myE (option string) :=
  match names with
  | nil => Ret None
  | cons name rest =>
    mv <- get_env name ;;
    match mv with
    | Some v => Ret (Some v)
    | None => find_env_value rest
    end
  end.

End EffectOptionMatch.

Crane Extraction "effect_option_match" EffectOptionMatch.
