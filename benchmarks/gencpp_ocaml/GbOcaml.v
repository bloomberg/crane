(** Plain OCaml extraction of the [benchmarks/gencpp] workloads.  [nat] is
    OCaml's [int], and the arithmetic Crane's NatIntStd maps to [uint64_t]
    operators maps to OCaml's integer operators here. *)
From Stdlib Require Import Extraction ExtrOcamlNatInt PeanoNat.
From GenCppBench Require GbBst GbLists GbInterp GbClo GbMaps.

Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.mul => "( * )".
Extract Constant Nat.sub => "fun n m -> Stdlib.max 0 (n-m)".
Extract Constant Nat.div => "fun n m -> if m = 0 then 0 else n / m".
Extract Constant Nat.modulo => "fun n m -> if m = 0 then n else n mod m".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.eqb => "(=)".

Extract Inlined Constant GbBst.GbBst.m_lcg => "65537".
Extract Inlined Constant GbLists.GbLists.m_lcg => "65537".
Extract Inlined Constant GbLists.GbLists.m_sum => "65535".
Extract Inlined Constant GbLists.GbLists.m_val => "4096".
Extract Inlined Constant GbInterp.GbInterp.m_lcg => "65537".
Extract Inlined Constant GbInterp.GbInterp.m_val => "4096".
Extract Inlined Constant GbInterp.GbInterp.fuel_big => "100000000".
Extract Inlined Constant GbClo.GbClo.m_lcg => "65537".
Extract Inlined Constant GbClo.GbClo.m_clo => "4093".
Extract Inlined Constant GbMaps.GbMaps.m_lcg => "65537".
Extract Inlined Constant GbMaps.GbMaps.m_sum => "65535".
Extract Inlined Constant GbMaps.GbMaps.m_key => "4000".
Extract Inlined Constant GbMaps.GbMaps.m_map => "1000".

Extraction "gb_bst.ml" GbBst.GbBst.bst.
Extraction "gb_lists.ml" GbLists.GbLists.lists.
Extraction "gb_interp.ml" GbInterp.GbInterp.interp.
Extraction "gb_clo.ml" GbClo.GbClo.closures.
Extraction "gb_maps.ml" GbMaps.GbMaps.maps.
