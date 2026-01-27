(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import
  Program.Wf.

Module Nat.

  Axiom int : Type.
  Axiom zero : int.
  Axiom one : int.
  Axiom positive : int -> bool.
  Axiom iplus : int -> int -> int.
  Axiom iminus : int -> int -> int.

  Inductive nat : Type :=
  | O : nat
  | S (n : nat) : nat.

  Fixpoint add (m : nat) (n : nat) : nat :=
    match m with
    | O => n
    | S x => S (add x n)
    end.

  Fixpoint nat_to_int (n : nat) : int :=
    match n with
    | O => zero
    | S n' => iplus one (nat_to_int n')
    end.

(*
  Axiom fuel : int -> Datatypes.nat.
  Axiom good_fuel1 : forall x, (forall x0 : int, fuel x0 < fuel x -> nat) -> fuel (iminus x one) < fuel x.
  Axiom good_fuel2 : well_founded (MR lt (fun x : int => fuel x)).

  Program Fixpoint int_to_nat (x : int)
    { measure (fuel x) } : nat :=
    if negb (positive x) then
      O
    else
      S (int_to_nat (iminus x one)).
  Next Obligation.
  Proof.
    apply good_fuel1; assumption.
  Qed.
  Next Obligation.
  Proof.
    apply good_fuel2.
  Qed.
*)

End Nat.

Require Crane.Extraction.
Require Import Crane.Mapping.BDE.


Crane Extract Inlined Constant Nat.int => "int".
Crane Extract Inlined Constant Nat.zero => "0".
Crane Extract Inlined Constant Nat.one => "1".
Crane Extract Inlined Constant Nat.iplus => "%a0 + %a1".
Crane Extract Inlined Constant Nat.iminus => "%a0 - %a1".
Crane Extract Inlined Constant Nat.positive => "%a0 > 0". (*
Crane Extract Inlined Constant Nat.fuel => "FUEL".

Crane Extract Inductive bool => "bool" [ "true" "false" ] "if(%scrut){%br0} else{%br1}".
Crane Extract Inlined Constant negb => "!(%a0)".
*)


Set Crane BDE Directory "~/bde_install/".
Crane Extraction "nat_bde" Nat.
