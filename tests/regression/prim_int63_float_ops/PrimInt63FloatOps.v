(** The PrimInt63 and PrimFloat primitives [Mapping.Std] mapped last
    (crane_int63.h, crane_float.h): signed readings, carrying arithmetic,
    exact products and divisions, leading and trailing zeros, the float
    comparison and the exponent primitives.  Each check compares a
    primitive's result at an edge case with the value Rocq computes; [Eval]
    below shows they all hold in Rocq, and the C++ checks them again.
    Found missing in the audit after Ephyra round 20 ([prim_array_default]):
    they extracted as unrealized axioms. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimInt63 PrimFloat CarryType.
From Stdlib Require Import List.
Import ListNotations.
Open Scope uint63_scope.

Module PrimInt63FloatOps.

Definition max := 9223372036854775807.
Definition min_s := 4611686018427387904. (* -2^62 read signed *)
Definition minus (x : int) : int := PrimInt63.sub 0 x.

Definition pair_is (p : int * int) (a b : int) : bool :=
  andb (PrimInt63.eqb (fst p) a) (PrimInt63.eqb (snd p) b).

Definition carry_is (c : carry int) (high : bool) (v : int) : bool :=
  match c with
  | C0 r => andb (negb high) (PrimInt63.eqb r v)
  | C1 r => andb high (PrimInt63.eqb r v)
  end.

Definition cmp_is (c : comparison) (d : comparison) : bool :=
  match c, d with Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end.

Definition int_checks : list bool :=
  [ PrimInt63.eqb (PrimInt63.asr min_s 1) 6917529027641081856;
    PrimInt63.eqb (PrimInt63.asr max 70) 0;
    PrimInt63.eqb (PrimInt63.asr 40 3) 5;
    PrimInt63.eqb (PrimInt63.divs min_s max) min_s;
    PrimInt63.eqb (PrimInt63.divs (minus 7) 2) (minus 3);
    PrimInt63.eqb (PrimInt63.mods (minus 7) 2) (minus 1);
    PrimInt63.eqb (PrimInt63.divs 5 0) 0;
    PrimInt63.eqb (PrimInt63.mods 5 0) 5;
    PrimInt63.ltsb (minus 1) 0;
    negb (PrimInt63.ltsb 0 (minus 1));
    PrimInt63.lesb min_s (minus 1);
    cmp_is (PrimInt63.compare max 1) Gt;
    cmp_is (PrimInt63.compares max 1) Lt;
    cmp_is (PrimInt63.compares 3 3) Eq;
    PrimInt63.eqb (PrimInt63.head0 0) 63;
    PrimInt63.eqb (PrimInt63.head0 1) 62;
    PrimInt63.eqb (PrimInt63.head0 max) 0;
    PrimInt63.eqb (PrimInt63.tail0 0) 63;
    PrimInt63.eqb (PrimInt63.tail0 8) 3;
    PrimInt63.eqb (PrimInt63.addmuldiv 0 12 max) 12;
    PrimInt63.eqb (PrimInt63.addmuldiv 63 12 max) max;
    PrimInt63.eqb (PrimInt63.addmuldiv 4 3 max) 63;
    PrimInt63.eqb (PrimInt63.addmuldiv 70 3 max) 0;
    pair_is (PrimInt63.mulc max max) 9223372036854775806 1;
    pair_is (PrimInt63.mulc 6 7) 0 42;
    pair_is (PrimInt63.mulc min_s 4) 2 0;
    pair_is (PrimInt63.diveucl 17 5) 3 2;
    pair_is (PrimInt63.diveucl 17 0) 0 17;
    pair_is (PrimInt63.diveucl_21 3 7 10) 2767011611056432743 1;
    pair_is (PrimInt63.diveucl_21 10 0 3) 0 0;
    carry_is (PrimInt63.addc max 1) true 0;
    carry_is (PrimInt63.addc 1 2) false 3;
    carry_is (PrimInt63.addcarryc max 0) true 0;
    carry_is (PrimInt63.addcarryc 1 2) false 4;
    carry_is (PrimInt63.subc 0 1) true max;
    carry_is (PrimInt63.subc 5 5) false 0;
    carry_is (PrimInt63.subcarryc 5 4) false 0;
    carry_is (PrimInt63.subcarryc 4 4) true max ].

Definition fcmp_is (c d : float_comparison) : bool :=
  match c, d with
  | FEq, FEq | FLt, FLt | FGt, FGt | FNotComparable, FNotComparable => true
  | _, _ => false
  end.

Definition nan : float := PrimFloat.div 0 0.

Definition float_checks : list bool :=
  [ fcmp_is (PrimFloat.compare 1 2) FLt;
    fcmp_is (PrimFloat.compare 2 1) FGt;
    fcmp_is (PrimFloat.compare 0 (PrimFloat.opp 0)) FEq;
    fcmp_is (PrimFloat.compare nan 1) FNotComparable;
    PrimInt63.eqb (PrimFloat.normfr_mantissa 0.75) 6755399441055744;
    PrimInt63.eqb (PrimFloat.normfr_mantissa (PrimFloat.opp 0.5)) 4503599627370496;
    PrimInt63.eqb (PrimFloat.normfr_mantissa 2) 0;
    PrimFloat.eqb (fst (PrimFloat.frshiftexp 3)) 0.75;
    PrimInt63.eqb (snd (PrimFloat.frshiftexp 3)) 2103;
    PrimInt63.eqb (snd (PrimFloat.frshiftexp 0)) 0;
    PrimFloat.eqb (PrimFloat.ldshiftexp 0.75 2103) 3;
    PrimFloat.eqb (PrimFloat.ldshiftexp 1 max) (PrimFloat.ldshiftexp 1 4202);
    PrimFloat.eqb (PrimFloat.next_up 1) 0x1.0000000000001p0;
    PrimFloat.eqb (PrimFloat.next_down 1) 0x1.fffffffffffffp-1;
    PrimFloat.ltb (PrimFloat.next_down 0) 0;
    PrimFloat.eqb (PrimFloat.next_up (PrimFloat.opp 0x1.fffffffffffffp1023)) (PrimFloat.opp 0x1.ffffffffffffep1023) ].

Fixpoint count_true (l : list bool) : nat :=
  match l with [] => 0 | b :: r => (if b then 1 else 0) + count_true r end.

Definition int_passed : nat := count_true int_checks.
Definition int_total : nat := length int_checks.
Definition float_passed : nat := count_true float_checks.
Definition float_total : nat := length float_checks.

End PrimInt63FloatOps.

Eval vm_compute in
  (PrimInt63FloatOps.int_passed, PrimInt63FloatOps.int_total,
   PrimInt63FloatOps.float_passed, PrimInt63FloatOps.float_total).

Crane Extraction "prim_int63_float_ops" PrimInt63FloatOps.
