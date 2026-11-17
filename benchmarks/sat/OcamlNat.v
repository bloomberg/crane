(** Native-int realizers for the [nat] operations the benchmark uses, so the
    OCaml side does not pay for Peano arithmetic that Crane maps to machine
    integers. *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt PeanoNat.
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(fun a b -> if a > b then a - b else 0)".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.div => "(fun a b -> if b = 0 then 0 else a / b)".
Extract Inlined Constant Nat.modulo => "(fun a b -> if b = 0 then a else a mod b)".
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.pred => "(fun a -> if a > 0 then a - 1 else 0)".
