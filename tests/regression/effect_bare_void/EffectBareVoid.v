(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: void-returning effects used as bare function bodies
   (without explicit bind or Ret tt sequencing).
   Tests whether gen_stmts correctly handles void calls in tail position
   when the function return type is void.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectBareVoid.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Bare print_endline as function body (no bind, no Ret) *)
  Definition just_print (msg : string) : itree myE unit :=
    print_endline msg.

  (** 2. Bare set_env as function body *)
  Definition just_set (k v : string) : itree myE unit :=
    set_env k v.

  (** 3. Print then Ret tt (normal pattern for comparison) *)
  Definition print_then_ret (msg : string) : itree myE unit :=
    print_endline msg ;;
    Ret tt.

  (** 4. Void effect in conditional — both branches are bare effects *)
  Definition cond_print (flag : bool) (msg : string) : itree myE unit :=
    if flag then
      print_endline msg
    else
      Ret tt.

  (** 5. Set env then print (chained void effects) *)
  Definition set_then_print (k v : string) : itree myE unit :=
    set_env k v ;;
    print_endline v.

  (** 6. Bare get_line (value-returning effect as sole body) *)
  Definition just_read : itree myE string :=
    get_line.

  (** 7. Bare get_env (value-returning, returns option) *)
  Definition just_get_env (name : string) : itree myE (option string) :=
    get_env name.

End EffectBareVoid.

Crane Extraction "effect_bare_void" EffectBareVoid.
