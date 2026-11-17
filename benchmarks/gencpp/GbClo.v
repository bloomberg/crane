(** Workloads for measuring the C++ Crane generates: persistent trees, list
    pipelines, an interpreter, closures and a balanced map from the standard
    library.  Each entry point folds its result into one number. *)
From Stdlib Require Import List PeanoNat FMapAVL OrderedTypeEx.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.
Import ListNotations.

Module GbClo.

(** Moduli and fuel, given as C++ literals: a closed [nat] product would be
    reduced to a unary numeral during extraction. *)
Axiom m_lcg m_sum m_clo m_val m_key m_map fuel_big : nat.

(** Pseudo-random numbers: a linear congruential step of the ZX81, kept below 65537. *)
Definition next (s : nat) : nat := (s * 75 + 74) mod m_lcg.

Fixpoint randoms (n s : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => s :: randoms n' (next s)
  end.

(** Closures: partially applied functions stored in a list and composed. *)
Definition compose (f g : nat -> nat) : nat -> nat := fun x => f (g x).

Fixpoint build (n : nat) : list (nat -> nat) :=
  match n with
  | 0 => []
  | S m => (fun x => (x * 3 + n) mod m_clo) :: build m
  end.

Definition closures (n rounds : nat) : nat :=
  let fs := build n in
  let big := fold_right compose (fun x => x) fs in
  fold_left (fun acc i => acc + big i + fold_left (fun a f => f a) fs i) (seq 0 rounds) 0.

End GbClo.

Crane Extract Inlined Constant GbClo.m_lcg => "UINT64_C(65537)".
Crane Extract Inlined Constant GbClo.m_sum => "UINT64_C(65535)".
Crane Extract Inlined Constant GbClo.m_clo => "UINT64_C(4093)".
Crane Extract Inlined Constant GbClo.m_val => "UINT64_C(4096)".
Crane Extract Inlined Constant GbClo.m_key => "UINT64_C(4000)".
Crane Extract Inlined Constant GbClo.m_map => "UINT64_C(1000)".
Crane Extract Inlined Constant GbClo.fuel_big => "UINT64_C(100000000)".
Set Crane Loopify.
Crane Extraction "gb_clo" GbClo.
