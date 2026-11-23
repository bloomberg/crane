(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Callables crossing between spellings (typed CppIR design, phase B1):
    each kind of source -- a global declared flat, a curried local, a
    lambda, the value of a let, of a match, of a local fixpoint applied
    partially, of an inline mapping -- put in each kind of slot -- a
    declared parameter, a type-variable parameter, an inline mapping's
    [auto], a loop variable (a fold's accumulator), a return, a let, a
    record field, an erased slot (a dependent pair's witness) -- at two and
    three arguments.  The suite compiles with [CRANE_STRICT_ARITY], so a
    crossing lowering misses is a compile error. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module CallableCrossingMatrix.

Definition add2 (a b : nat) : nat := a + b.
Definition add3 (a b c : nat) : nat := a + b + c.

(** An inline mapping whose parameter is a type variable: C++ deduces
    [auto]. *)
Definition keep {A} (x : A) : A := x.
Crane Extract Inlined Constant keep => "%a0".

Definition idp {A} (x : A) : A := x.

(** Slots. *)
Definition at_param2 (f : nat -> nat -> nat) : nat := f 1 2.
Definition at_param3 (f : nat -> nat -> nat -> nat) : nat := f 1 2 3.
Definition at_tvar2 (f : nat -> nat -> nat) : nat := idp f 1 2.
Definition at_tvar3 (f : nat -> nat -> nat -> nat) : nat := idp f 1 2 3.
Definition at_auto2 (f : nat -> nat -> nat) : nat := keep f 1 2.
Definition at_auto3 (f : nat -> nat -> nat -> nat) : nat := keep f 1 2 3.

Definition at_loop2 (f : nat -> nat -> nat) : nat :=
  fold_left (fun (g : nat -> nat -> nat) (_ : nat) => g) [1; 2] f 1 2.
Definition at_loop3 (f : nat -> nat -> nat -> nat) : nat :=
  fold_left (fun (g : nat -> nat -> nat -> nat) (_ : nat) => g) [1; 2] f 1 2 3.

Definition at_return2 (f : nat -> nat -> nat) : nat -> nat -> nat := f.
Definition at_return3 (f : nat -> nat -> nat -> nat) : nat -> nat -> nat -> nat := f.

Definition at_let2 (f : nat -> nat -> nat) : nat := let g := f in g 1 2.
Definition at_let3 (f : nat -> nat -> nat -> nat) : nat := let g := f in g 1 2 3.

Record holder2 := { h2 : nat -> nat -> nat }.
Record holder3 := { h3 : nat -> nat -> nat -> nat }.
Definition at_field2 (f : nat -> nat -> nat) : nat := h2 {| h2 := f |} 1 2.
Definition at_field3 (f : nat -> nat -> nat -> nat) : nat := h3 {| h3 := f |} 1 2 3.

Definition at_erased2 (f : nat -> nat -> nat) : nat :=
  match existT (fun T : Type => T) (nat -> nat -> nat) f with existT _ _ g => 0 end
  + f 1 2.

(** Sources. *)
Definition curried2 : nat -> nat -> nat := fun a => fun b => a + b.
Definition curried3 : nat -> nat -> nat -> nat := fun a => fun b => fun c => a + b + c.

Definition src_lambda2 := fun a b : nat => a + b.
Definition src_let2 (n : nat) : nat -> nat -> nat := let k := n in fun a b => a + b + k.
Definition src_match2 (n : nat) : nat -> nat -> nat :=
  match n with O => add2 | S _ => fun a b => b + a end.
Definition src_fix2 (n : nat) : nat -> nat -> nat :=
  (fix go (m a b : nat) : nat := match m with O => a + b | S m' => go m' a b end) n.
Definition src_fix3 (n : nat) : nat -> nat -> nat -> nat :=
  (fix go (m a b c : nat) : nat := match m with O => a + b + c | S m' => go m' a b c end) n.
Definition src_mapping2 : nat -> nat -> nat := keep add2.

Definition sum2 (slot : (nat -> nat -> nat) -> nat) : nat :=
  slot add2 + slot curried2 + slot src_lambda2 + slot (src_let2 0)
  + slot (src_match2 0) + slot (src_fix2 1) + slot src_mapping2.

Definition sum3 (slot : (nat -> nat -> nat -> nat) -> nat) : nat :=
  slot add3 + slot curried3 + slot (fun a b c => a + b + c) + slot (src_fix3 1).

Definition r2_param := sum2 at_param2.
Definition r2_tvar := sum2 at_tvar2.
Definition r2_auto := sum2 at_auto2.
Definition r2_loop := sum2 at_loop2.
Definition r2_return := sum2 (fun f => at_return2 f 1 2).
Definition r2_let := sum2 at_let2.
Definition r2_field := sum2 at_field2.
Definition r2_erased := sum2 at_erased2.

Definition r3_param := sum3 at_param3.
Definition r3_tvar := sum3 at_tvar3.
Definition r3_auto := sum3 at_auto3.
Definition r3_loop := sum3 at_loop3.
Definition r3_return := sum3 (fun f => at_return3 f 1 2 3).
Definition r3_let := sum3 at_let3.
Definition r3_field := sum3 at_field3.

End CallableCrossingMatrix.

Crane Extraction "callable_crossing_matrix" CallableCrossingMatrix.
