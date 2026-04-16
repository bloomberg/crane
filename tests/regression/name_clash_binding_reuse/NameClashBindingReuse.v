From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashBindingReuse.

(** Test: structured binding names (d_a0 etc.) reused across matches.
    Particularly tricky when matches are NOT wrapped in IIFEs
    (i.e. statement-position matches vs expression-position matches). *)

Inductive pair_nat : Type :=
| MkPairNat : nat -> nat -> pair_nat.

(** Two matches in sequence, both on pair_nat.
    Both generate d_a0, d_a1 structured bindings. *)
Definition add_pairs (p1 p2 : pair_nat) : nat :=
  match p1 with
  | MkPairNat a1 b1 =>
    match p2 with
    | MkPairNat a2 b2 => a1 + b1 + a2 + b2
    end
  end.

(** Same but as let-bindings (each match is an expression → IIFE). *)
Definition add_pairs_let (p1 p2 : pair_nat) : nat :=
  let sum1 := match p1 with MkPairNat a b => a + b end in
  let sum2 := match p2 with MkPairNat a b => a + b end in
  sum1 + sum2.

Inductive triple_nat : Type :=
| MkTripleNat : nat -> nat -> nat -> triple_nat.

(** Nested match: outer match on triple, inner match on pair.
    Both have d_a0, d_a1; inner should get d_a00, d_a10. *)
Definition combine (t : triple_nat) (p : pair_nat) : nat :=
  match t with
  | MkTripleNat x y z =>
    match p with
    | MkPairNat a b => x + y + z + a + b
    end
  end.

(** Match where the binding variable is used as scrutinee of another match *)
Definition cascade (t : triple_nat) : pair_nat :=
  match t with
  | MkTripleNat x y z => MkPairNat (x + y) z
  end.

Definition cascade_and_match (t : triple_nat) : nat :=
  match cascade t with
  | MkPairNat a b => a + b
  end.

(** Single-constructor match inside single-constructor match.
    Neither needs an if guard, just structured bindings.
    Could be tricky if both are in the same block without scoping. *)
Definition flat_combine (p1 p2 : pair_nat) : pair_nat :=
  match p1 with
  | MkPairNat a1 b1 =>
    match p2 with
    | MkPairNat a2 b2 => MkPairNat (a1 + a2) (b1 + b2)
    end
  end.

End NameClashBindingReuse.

Crane Extraction "name_clash_binding_reuse" NameClashBindingReuse.
