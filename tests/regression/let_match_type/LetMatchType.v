(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tests for let-binding match expressions.
    Targets the type inference of variables that hold match results. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module LetMatchType.

(** 1. let-bound bool match returning nat *)
Definition let_match_nat (b : bool) : nat :=
  let x := if b then 1 else 0 in
  x + x.

(** 2. let-bound nat match returning string — TRIGGERS std::any bug *)
Definition let_match_string (n : nat) : string :=
  let s := match n with
    | O => "zero"
    | _ => "nonzero"
    end in
  cat s s.

(** 3. let-bound option match *)
Definition let_match_option (o : option nat) : nat :=
  let x := match o with
    | Some n => n
    | None => 0
    end in
  x + 1.

(** 4. let-bound nested bool match *)
Definition let_nested_bool (a b : bool) : nat :=
  let x := if a then (if b then 3 else 2) else (if b then 1 else 0) in
  x.

(** 5. Multiple let-bound matches *)
Definition multi_let_match (a b : bool) : nat :=
  let x := if a then 10 else 0 in
  let y := if b then 1 else 0 in
  x + y.

(** 6. let-bound match used in function argument *)
Definition let_match_in_arg (n : nat) : nat :=
  let x := match n with O => 0 | S n' => n' end in
  Nat.add x x.

(** 7. let-bound match in monadic context *)
Definition let_match_monadic (b : bool) : itree ioE string :=
  let msg := if b then "yes" else "no" in
  print_endline msg ;;
  Ret msg.

(** 8. let-bound match of custom type *)
Inductive direction := North | South | East | West.

Definition direction_offset (d : direction) : nat * nat :=
  let dx := match d with East => 1 | West => 2 | _ => 0 end in
  let dy := match d with North => 1 | South => 2 | _ => 0 end in
  (dx, dy).

End LetMatchType.

Crane Extraction "let_match_type" LetMatchType.
