(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: option match in various contexts where branches produce
   string variables vs string literals, stressing IIFE return type
   deduction and custom match template expansion.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectOptionString.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Pure let binding with option match — Some returns variable,
      None returns string literal *)
  Definition let_option_match (name : string) : itree myE string :=
    r <- get_env name ;;
    let s := match r with
      | Some v => v
      | None => "unknown"
    end in
    Ret s.

  (** 2. Option match as bind action — Some returns Ret of variable,
      None returns Ret of string literal *)
  Definition bind_option_match (name : string) : itree myE string :=
    r <- get_env name ;;
    result <- match r with
      | Some v => Ret v
      | None => Ret "fallback"
    end ;;
    Ret result.

  (** 3. Option match where Some arm has an effect and None arm returns literal *)
  Definition option_effect_or_literal (name : string) : itree myE string :=
    r <- get_env name ;;
    match r with
    | Some _ =>
      line <- get_line ;;
      Ret line
    | None =>
      Ret "no_input"
    end.

  (** 4. Nested option matches: match on option, inside Some branch
      do another get_env and match *)
  Definition nested_option (n1 n2 : string) : itree myE string :=
    r1 <- get_env n1 ;;
    match r1 with
    | Some v1 =>
      r2 <- get_env n2 ;;
      match r2 with
      | Some v2 => Ret (cat v1 (cat "/" v2))
      | None => Ret v1
      end
    | None => Ret "none"
    end.

  (** 5. Option match result fed directly to an effect *)
  Definition option_then_effect (name : string) : itree myE unit :=
    r <- get_env name ;;
    let msg := match r with
      | Some v => v
      | None => "not_set"
    end in
    print_endline msg.

  (** 6. Option match with int result *)
  Definition option_int (name : string) : itree myE int :=
    r <- get_env name ;;
    let len := match r with
      | Some v => PrimString.length v
      | None => 0%int63
    end in
    Ret len.

End EffectOptionString.

Crane Extraction "effect_option_string" EffectOptionString.
