(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: higher-order functions with void-returning effect callbacks.
   Exercises: void callback detection, unit parameter erasure,
   template parameter void wrapping, and recursive HOF with effects.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectHofVoid.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Apply a void callback *)
  Definition apply_void (f : string -> itree myE unit) (x : string)
    : itree myE unit :=
    f x.

  (** 2. Apply a void callback then return a value *)
  Definition apply_then_return (f : string -> itree myE unit) (x : string)
    : itree myE string :=
    f x ;;
    Ret x.

  (** 3. Apply a value callback *)
  Definition apply_value (f : string -> itree myE string) (x : string)
    : itree myE string :=
    result <- f x ;;
    Ret result.

  (** 4. Apply callback conditionally *)
  Definition apply_if (flag : bool) (f : string -> itree myE unit) (x : string)
    : itree myE unit :=
    if flag then f x
    else Ret tt.

  (** 5. Chain two void callbacks *)
  Definition chain_void (f g : string -> itree myE unit) (x : string)
    : itree myE unit :=
    f x ;;
    g x.

  (** 6. Apply a callback N times *)
  Fixpoint apply_n (f : string -> itree myE unit) (x : string) (n : nat)
    : itree myE nat :=
    match n with
    | O => Ret O
    | S n' =>
      f x ;;
      rest <- apply_n f x n' ;;
      Ret (S rest)
    end.

  (** 7. Use print_endline as a concrete callback *)
  Definition concrete_use : itree myE string :=
    apply_then_return print_endline "hello".

  (** 8. Use set_env as a concrete callback via wrapper *)
  Definition set_wrapper (v : string) : string -> itree myE unit :=
    fun k => set_env k v.

  Definition concrete_set : itree myE unit :=
    let f := set_wrapper "myval" in
    f "mykey".

End EffectHofVoid.

Crane Extraction "effect_hof_void" EffectHofVoid.
