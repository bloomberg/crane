(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt ExtrOcamlZInt.
From Stdlib Require BinNums PeanoNat BinPos BinNat BinInt Ascii.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import IntDFA.

(* Parity with CraneExtraction.v.  Whatever the C++ side represents natively,
   this side does too, so the comparison measures the two compilers rather
   than two representations.  Crane loads Mapping.NatIntStd ([nat] ->
   uint64_t) and Mapping.ZInt, which re-exports Mapping.NInt ([N] and
   [positive] -> unsigned int, [Z] -> int64_t), each with its arithmetic
   inlined; ExtrOcamlNatInt and ExtrOcamlZInt give the types the same native
   [int] representation, and the operations below are the ones those two
   files leave as recursive definitions. *)
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Constant Nat.div => "fun a b -> if b = 0 then 0 else a / b".
Extract Constant Nat.modulo => "fun a b -> if b = 0 then a else a mod b".
Extract Constant Nat.double => "fun a -> a + a".
Extract Constant Nat.iter =>
  "fun n f x -> let rec go n x = if n <= 0 then x else go (n - 1) (f x) in go n x".
Extract Inlined Constant PeanoNat.Nat.ltb => "(<)".
Extract Inlined Constant PeanoNat.Nat.leb => "(<=)".
Extract Inlined Constant PeanoNat.Nat.eqb => "(=)".
Extract Constant PeanoNat.Nat.div => "fun a b -> if b = 0 then 0 else a / b".
Extract Constant PeanoNat.Nat.modulo => "fun a b -> if b = 0 then a else a mod b".
Extract Constant PeanoNat.Nat.double => "fun a -> a + a".
(* [positive]'s doubling constructors saturate at [max_int] rather than wrap:
   a fuel bound such as DFA.v's [Brzozowski_bound], 2^(n+1) - 1 for a regex of
   length n, is 2^63 - 1 or more past n = 61, and wrapped to -1 it reads as no
   fuel at all -- the table is not filled, and the lexer falls back to
   saturating each DFA.  Crane's [unsigned int] keeps it at UINT_MAX, whose
   doubling plus one is UINT_MAX again.  Below [max_int] nothing changes. *)
Extract Inductive BinNums.positive => int
  [ "(fun p -> if p >= Stdlib.max_int / 2 then Stdlib.max_int else 1 + 2 * p)"
    "(fun p -> if p > Stdlib.max_int / 2 then Stdlib.max_int else 2 * p)"
    "1" ]
  "(fun f2p1 f2p f1 p -> if p <= 1 then f1 () else if p mod 2 = 0 then f2p (p / 2) else f2p1 (p / 2))".
Extract Inlined Constant BinPos.Pos.eqb => "(=)".
Extract Inlined Constant BinPos.Pos.ltb => "(<)".
Extract Inlined Constant BinPos.Pos.leb => "(<=)".
Extract Constant BinPos.Pos.of_nat => "fun n -> Stdlib.max 1 n".
Extract Constant BinPos.Pos.to_nat => "fun p -> p".
Extract Inlined Constant BinNat.N.eqb => "(=)".
Extract Inlined Constant BinNat.N.ltb => "(<)".
Extract Inlined Constant BinNat.N.leb => "(<=)".
Extract Constant BinNat.N.double => "fun n -> 2 * n".
Extract Constant BinNat.N.succ_double => "fun n -> 2 * n + 1".
Extract Constant BinNat.N.of_nat => "fun n -> n".
Extract Constant BinNat.N.to_nat => "fun n -> n".
Extract Inlined Constant BinInt.Z.eqb => "(=)".
Extract Inlined Constant BinInt.Z.ltb => "(<)".
Extract Inlined Constant BinInt.Z.leb => "(<=)".
Extract Inlined Constant BinInt.Z.gtb => "(>)".
Extract Inlined Constant BinInt.Z.geb => "(>=)".
(* [Z.div]/[Z.modulo] round toward negative infinity, as Rocq defines them. *)
Extract Constant BinInt.Z.div =>
  "fun a b -> if b = 0 then 0 else let q = a / b in if (a mod b <> 0) && ((a < 0) <> (b < 0)) then q - 1 else q".
Extract Constant BinInt.Z.modulo =>
  "fun a b -> if b = 0 then a else let r = a mod b in if r <> 0 && ((r < 0) <> (b < 0)) then r + b else r".
Extract Constant BinInt.Z.of_nat => "fun n -> n".
Extract Constant BinInt.Z.to_nat => "fun z -> Stdlib.max 0 z".
Extract Constant BinInt.Z.to_N => "fun z -> Stdlib.max 0 z".

(* The character operations CraneExtraction.v inlines. *)
Extract Constant Ascii.compare =>
  "fun a b -> let c = Stdlib.Char.compare a b in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt".
Extract Inlined Constant Ascii.N_of_ascii => "Stdlib.Char.code".

(* The interned DFA's transition rows, as CraneExtraction.v realizes them
   with immer::flex_vector: an array, built once from a list and then only
   indexed.  [vec_nth] is a bounds-checked [Array.get], and a character's
   column is computed rather than searched for -- with the same assumption
   CraneExtraction.v's [idx_of_eqb] makes, that the alphabet is ASCII
   enumerated in descending order; the functor's alphabet type is abstract,
   hence [Obj.magic]. *)
Extract Inductive IntDFA.vec => "array"
  [ "[||]" "(fun (h, t) -> Stdlib.Array.append [|h|] t)" ]
  "(fun fnil fcons v -> if Stdlib.Array.length v = 0 then fnil () else fcons (Stdlib.Array.get v 0) (Stdlib.Array.sub v 1 (Stdlib.Array.length v - 1)))".
Extract Inlined Constant IntDFA.vec_of_list => "Stdlib.Array.of_list".
Extract Constant IntDFA.vec_nth =>
  "fun v n d -> if n < Stdlib.Array.length v then Stdlib.Array.get v n else d".
Extract Constant IntDFA.idx_of_eqb =>
  "fun _ a _ -> 255 - Stdlib.Char.code (Obj.magic a)".
