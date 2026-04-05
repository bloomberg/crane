(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests for match/conditional expressions used as the ACTION side of a bind.
   E.g., [x <- (if b then effect1 else effect2) ;; ...].
   This exercises how gen_stmts handles monadic match in expression context.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO Monads.Env Monads.Clock.
Local Open Scope pstring_scope.

Module EffectBindAction.

  Definition myE := ioE +' envE +' clockE.
  Crane Extract Skip myE.

  (** 1. Bool match inside bind action: one branch block template *)
  Definition conditional_read (use_stdin : bool) : itree myE string :=
    line <- (if use_stdin then get_line else Ret "default") ;;
    Ret line.

  (** 2. Bool match where both branches are effects *)
  Definition conditional_effect (flag : bool) : itree myE int :=
    t <- (if flag then steady_now else Ret 0%int63) ;;
    Ret t.

  (** 3. Option match inside bind: conditional effect based on env *)
  Definition maybe_override (name default : string) : itree myE string :=
    r <- get_env name ;;
    result <- (match r with
               | Some v => Ret v
               | None => Ret default
               end) ;;
    Ret result.

  (** 4. Nested: effect result used in another conditional effect *)
  Definition timed_if_needed (measure : bool) : itree myE (int * int) :=
    t1 <- (if measure then steady_now else Ret 0%int63) ;;
    t2 <- (if measure then steady_now else Ret 0%int63) ;;
    Ret (t1, t2).

  (** 5. Block template get_line, then conditional print *)
  Definition echo_if (flag : bool) : itree myE string :=
    line <- get_line ;;
    (if flag then print_endline line else Ret tt) ;;
    Ret line.

  (** 6. Effect action that's a function application (not inlined) *)
  Definition helper (s : string) : itree myE string :=
    print_endline s ;;
    Ret s.

  Definition use_helper (flag : bool) : itree myE string :=
    r <- (if flag then helper "yes" else helper "no") ;;
    Ret r.

  (** 7. Let-binding of a match result, then use in effect *)
  Definition let_match_then_effect (n : nat) : itree myE string :=
    let msg := match n with O => "zero" | _ => "other" end in
    print_endline msg ;;
    Ret msg.

  (** 8. Discard result of conditional effect *)
  Definition discard_conditional (flag : bool) : itree myE nat :=
    _ <- (if flag then print_endline "flagged" else Ret tt) ;;
    Ret 42.

End EffectBindAction.

Crane Extraction "effect_bind_action" EffectBindAction.
