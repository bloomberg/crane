(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: match/conditional expressions as arguments to effect functions.
   When [set_env key value] is called and [value] is a match expression,
   the C++ ternary [flag ? "yes"s : "no"s] is substituted for [%a1] in
   [setenv(%a0.c_str(), %a1.c_str(), 1)].  The [.c_str()] binds to
   ["no"s] only (member access has highest precedence), producing
   [flag ? "yes"s : "no"s.c_str()] where the ternary resolves to
   [std::string] but [setenv] expects [const char*].
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectMatchArg.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Bool match as value argument to set_env *)
  Definition set_bool_value (flag : bool) (key : string) : itree myE unit :=
    set_env key (if flag then "yes" else "no").

  (** 2. Bool match as key argument to set_env *)
  Definition set_bool_key (flag : bool) (value : string) : itree myE unit :=
    set_env (if flag then "KEY_A" else "KEY_B") value.

  (** 3. Option match result as argument to set_env *)
  Definition set_option_value (key : string) (r : option string)
    : itree myE unit :=
    set_env key (match r with Some v => v | None => "default" end).

  (** 4. Bool match as argument to print_endline — exercises << precedence *)
  Definition print_conditional (flag : bool) : itree myE unit :=
    print_endline (if flag then "TRUE" else "FALSE").

  (** 5. Bool match as argument to get_env *)
  Definition get_conditional (flag : bool) : itree myE (option string) :=
    get_env (if flag then "KEY_A" else "KEY_B").

  (** 6. Chained: match result passed to set_env then get_env *)
  Definition round_trip_match (flag : bool) : itree myE (option string) :=
    let key := if flag then "X" else "Y" in
    set_env key "val" ;;
    get_env key.

End EffectMatchArg.

Crane Extraction "effect_match_arg" EffectMatchArg.
