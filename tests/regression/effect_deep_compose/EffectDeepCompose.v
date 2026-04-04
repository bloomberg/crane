(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Stress test for deep effect composition (3+ effects in one function).
   Tests that ReSum infrastructure types are properly erased.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
                          Monads.ITree Monads.IO Monads.Env Monads.Clock.
Local Open Scope pstring_scope.

Module EffectDeepCompose.

(** Composed effect: IO + Env + Clock *)
Definition bigE := ioE +' envE +' clockE.
Crane Extract Skip bigE.

(** 1. Function using all three effects *)
Definition timed_env_op (name value : string) : itree bigE int :=
  t1 <- steady_now ;;
  set_env name value ;;
  print_endline "env set" ;;
  t2 <- steady_now ;;
  Ret (PrimInt63.sub t2 t1).

(** 2. Function using only console from inside bigE *)
Definition just_greet : itree bigE unit :=
  print_endline "hello from bigE".

(** 3. Function using env + console but not clock *)
Definition env_with_log (name value : string) : itree bigE unit :=
  print_endline "setting env..." ;;
  set_env name value ;;
  print_endline "done".

(** 4. Read env, print result *)
Definition show_env (name : string) : itree bigE unit :=
  mv <- get_env name ;;
  match mv with
  | Some v => print_endline v
  | None => print_endline "not set"
  end.

(** 5. Conditional clock read *)
Definition maybe_time (measure : bool) : itree bigE int :=
  if measure then steady_now
  else Ret 0%int63.

(** 6. Recursive function over all three effects *)
Fixpoint repeat_n (n : nat) : itree bigE unit :=
  match n with
  | O => Ret tt
  | S n' =>
    _ <- steady_now ;;
    print_endline "tick" ;;
    repeat_n n'
  end.

End EffectDeepCompose.

Crane Extraction "effect_deep_compose" EffectDeepCompose.
