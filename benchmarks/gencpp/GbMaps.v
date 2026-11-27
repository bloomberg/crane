(** Workloads for measuring the C++ Crane generates: persistent trees, list
    pipelines, an interpreter, closures and a balanced map from the standard
    library.  Each entry point folds its result into one number. *)
From Stdlib Require Import List PeanoNat FMapAVL OrderedTypeEx.
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.
Import ListNotations.

Module GbMaps.

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

(** The standard library's AVL maps, as Vellvm uses them. *)
Module M := FMapAVL.Make Nat_as_OT.

Definition maps (n rounds : nat) : nat :=
  fold_left
    (fun acc i =>
       let m := fold_left (fun m x => M.add (x mod m_key) (x + i) m) (randoms n (i + 11)) (M.empty nat) in
       let m := M.map (fun v => v mod m_map) m in
       acc + M.fold (fun k v a => (a + k * v) mod m_sum) m 0
       + match M.find 17 m with Some v => v | None => 0 end)
    (seq 0 rounds) 0.


End GbMaps.

Crane Extract Inlined Constant GbMaps.m_lcg => "UINT64_C(65537)".
Crane Extract Inlined Constant GbMaps.m_sum => "UINT64_C(65535)".
Crane Extract Inlined Constant GbMaps.m_clo => "UINT64_C(4093)".
Crane Extract Inlined Constant GbMaps.m_val => "UINT64_C(4096)".
Crane Extract Inlined Constant GbMaps.m_key => "UINT64_C(4000)".
Crane Extract Inlined Constant GbMaps.m_map => "UINT64_C(1000)".
Crane Extract Inlined Constant GbMaps.fuel_big => "UINT64_C(100000000)".
Set Crane Loopify.
Crane Extraction "gb_maps" GbMaps.
