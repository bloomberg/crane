(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: complex expressions as arguments to effect functions.
   The key concern is operator precedence when inline custom templates
   like [setenv(%a0.c_str(), ...)] have complex subexpressions
   substituted for [%a0].

   When [%a0] is [cat "prefix_" suffix], the substitution produces
   ["prefix_"s + suffix.c_str()] — but [.c_str()] binds to [suffix],
   not to the whole concatenation. This is a precedence bug in
   placeholder expansion.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectComplexArgs.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. set_env with concatenated key — complex expr as first arg *)
  Definition set_prefixed (prefix suffix value : string) : itree myE unit :=
    set_env (cat prefix suffix) value.

  (** 2. set_env with concatenated value — complex expr as second arg *)
  Definition set_with_value (key prefix suffix : string) : itree myE unit :=
    set_env key (cat prefix suffix).

  (** 3. get_env with concatenated name *)
  Definition get_prefixed (prefix suffix : string) : itree myE (option string) :=
    get_env (cat prefix suffix).

  (** 4. print_endline with concatenated string *)
  Definition print_concat (a b : string) : itree myE unit :=
    print_endline (cat a b).

  (** 5. Chained: build key, set env, then get env *)
  Definition round_trip (prefix suffix value : string) : itree myE (option string) :=
    let key := cat prefix suffix in
    set_env key value ;;
    get_env key.

  (** 6. Nested concatenation as argument *)
  Definition deep_concat (a b c : string) : itree myE unit :=
    set_env (cat (cat a b) c) "value".

  (** 7. Effect result used in concatenation for another effect *)
  Definition chain_with_concat (name : string) : itree myE unit :=
    r <- get_env name ;;
    match r with
    | Some v => set_env (cat "COPY_" name) v
    | None => Ret tt
    end.

  (** 8. unset_env with concatenated key *)
  Definition unset_prefixed (prefix suffix : string) : itree myE unit :=
    unset_env (cat prefix suffix).

End EffectComplexArgs.

Crane Extraction "effect_complex_args" EffectComplexArgs.
