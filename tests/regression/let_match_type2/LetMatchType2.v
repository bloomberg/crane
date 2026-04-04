(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** More let-match type tests.
    Tests match returning different types to isolate the std::any bug. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module LetMatchType2.

(** 1. Match returning bool — should be fine *)
Definition let_match_bool (n : nat) : bool :=
  let b := match n with O => true | _ => false end in
  negb b.

(** 2. Match returning pair — might trigger std::any *)
Definition let_match_pair (b : bool) : nat :=
  let p := if b then (1, 2) else (3, 4) in
  fst p + snd p.

(** 3. Match returning list — might trigger std::any *)
Definition let_match_list (b : bool) : list nat :=
  let xs := if b then cons 1 nil else nil in
  xs.

(** 4. Match returning option — might trigger std::any *)
Definition let_match_opt (b : bool) : option nat :=
  let o := if b then Some 1 else None in
  o.

(** 5. Cascading let-matches all returning nat — should be fine *)
Definition cascading_nat (a b c : bool) : nat :=
  let x := if a then 10 else 0 in
  let y := if b then 5 else 0 in
  let z := if c then 1 else 0 in
  x + y + z.

(** 6. Match returning function type *)
Definition let_match_fun (b : bool) : nat :=
  let f := if b then S else fun n => n in
  f 5.

(** 7. Match result used in another match *)
Definition match_of_match (n : nat) : nat :=
  let x := match n with O => 1 | S _ => 2 end in
  match x with O => 100 | S O => 200 | _ => 300 end.

(** 8. let-bound match where arms have bindings *)
Definition let_match_bindings (n : nat) : nat :=
  let x := match n with
    | O => 0
    | S m => m + 1
    end in
  x + x.

End LetMatchType2.

Crane Extraction "let_match_type2" LetMatchType2.
