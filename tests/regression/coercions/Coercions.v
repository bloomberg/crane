(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Coercions — implicit term insertion by the elaborator. *)

From Stdlib Require Import Nat Bool.

Module Coercions.

(* === Basic coercion: bool -> nat === *)

Definition bool_to_nat (b : bool) : nat :=
  if b then 1 else 0.

Coercion bool_to_nat : bool >-> nat.

Definition add_bool (n : nat) (b : bool) : nat :=
  n + b.  (* b is coerced to nat *)

Definition test_add_true : nat := add_bool 5 true.
Definition test_add_false : nat := add_bool 5 false.

(* === Record coercion === *)

Record Wrapper := mkWrapper { unwrap : nat }.

Coercion unwrap : Wrapper >-> nat.

Definition double_wrapped (w : Wrapper) : nat :=
  w + w.  (* w is coerced via unwrap *)

Definition test_double_wrapped : nat := double_wrapped (mkWrapper 7).

(* === Chained coercion: bool -> nat via Wrapper === *)

Record BoolBox := mkBoolBox { unbox : bool }.

Coercion unbox : BoolBox >-> bool.
(* BoolBox -> bool -> nat via chain *)

Definition add_boolbox (n : nat) (bb : BoolBox) : nat :=
  n + bb.  (* bb coerced through bool then nat *)

Definition test_add_boolbox : nat := add_boolbox 10 (mkBoolBox true).

(* === Function coercion (fun class) === *)

Record Transform := mkTransform { apply_transform : nat -> nat }.

Coercion apply_transform : Transform >-> Funclass.

Definition double_transform : Transform := mkTransform (fun n => n + n).

Definition test_fun_coercion : nat := double_transform 5.

End Coercions.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "coercions" Coercions.
