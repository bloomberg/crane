(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Stress tests for unit handling in monadic/effect context.
    Targets edge cases in void-ification, bind flattening, and
    mixed unit/value chains. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module EffectUnitStress.

(** 1. Ret tt at different nesting depths *)
Definition ret_tt_simple : itree ioE unit := Ret tt.

Definition ret_tt_after_bind : itree ioE unit :=
  _ <- Ret tt ;; Ret tt.

Definition ret_tt_after_effect : itree ioE unit :=
  print_endline "x" ;; Ret tt.

(** 2. Bind where RHS is Ret of the LHS binding *)
Definition bind_identity : itree ioE string :=
  s <- get_line ;; Ret s.

(** 3. Bind where RHS ignores the binding *)
Definition bind_ignore : itree ioE nat :=
  _ <- get_line ;; Ret 0.

(** 4. Multiple Ret tt in if-then-else *)
Definition conditional_tt (b : bool) : itree ioE unit :=
  if b then Ret tt else Ret tt.

(** 5. Ret in one branch, effect in other *)
Definition conditional_mixed (b : bool) : itree ioE unit :=
  if b then print_endline "yes" else Ret tt.

(** 6. Tuple of monadic results *)
Definition pair_of_effects : itree ioE (string * string) :=
  a <- get_line ;;
  b <- get_line ;;
  Ret (a, b).

(** 7. match on nat with monadic body *)
Definition nat_dispatch (n : nat) : itree ioE string :=
  match n with
  | O => Ret "zero"
  | S O => Ret "one"
  | S (S _) => Ret "many"
  end.

(** 8. let in monadic context with pure computation *)
Definition let_pure_in_monadic : itree ioE int :=
  s <- get_line ;;
  let n := PrimString.length s in
  let m := PrimInt63.add n 1 in
  Ret m.

(** 9. Nested if in monadic context *)
Definition nested_if_monadic (b1 b2 : bool) : itree ioE string :=
  if b1
  then if b2 then Ret "both" else Ret "first"
  else if b2 then Ret "second" else Ret "neither".

(** 10. Monadic function returning option *)
Definition safe_head (xs : list nat) : itree ioE (option nat) :=
  match xs with
  | nil => print_endline "empty!" ;; Ret None
  | cons x _ => Ret (Some x)
  end.

End EffectUnitStress.

Crane Extraction "effect_unit_stress" EffectUnitStress.
