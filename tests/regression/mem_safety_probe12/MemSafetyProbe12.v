From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module MemSafetyProbe12.

(** Probe 12: Type-indexed inductives (existential types) with closures.

    When an inductive has type INDICES (not params), ind_nparams=0
    and field types are erased to std::any. Storing a closure in
    std::any and recovering it with any_cast requires the stored
    type to match exactly. A raw lambda type != std::function<T>.

    This is the known "std::any closure type mismatch" bug from
    existential_closure_probe. We reproduce it with different
    patterns to identify which ones crash and which are safe. *)

(** wrap : Set -> Type is a type-indexed inductive.
    ind_nparams = 0, so all field types become std::any. *)
Inductive wrap : Set -> Type :=
| Wrap : forall (A : Set), A -> wrap A.

(** Unwrap extracts the value from wrap A. *)
Definition unwrap {A : Set} (w : wrap A) : A :=
  match w with
  | Wrap _ a => a
  end.

(** TEST 1: Pack a NAT — should work since nat = unsigned int. *)
Definition pack_nat : wrap nat := Wrap nat 42.

Definition test_pack_nat : nat := unwrap pack_nat.
(** Expected: 42 *)

(** TEST 2: Pack a BOOL — tests non-function values. *)
Definition pack_bool : wrap bool := Wrap bool true.

Definition test_pack_bool : bool := unwrap pack_bool.
(** Expected: true *)

(** TEST 3: Pack a LET-BOUND closure.
    let f := fun x => x + base in Wrap (nat -> nat) f
    This should work because f has type std::function<...>
    by the time it's passed to Wrap. *)
Definition pack_fn_let (base : nat) : wrap (nat -> nat) :=
  let f := fun x => x + base in
  Wrap (nat -> nat) f.

Definition test_pack_fn_let : nat :=
  let w := pack_fn_let 10 in
  let f := unwrap w in
  f 5.
(** Expected: 15 *)

(** TEST 4: Pack a DIRECT lambda (no let-binding).
    Wrap (nat -> nat) (fun x => x + base)
    BUG: The raw lambda type is stored in std::any,
    but unwrap tries any_cast<std::function<...>>. *)
Definition pack_fn_direct (base : nat) : wrap (nat -> nat) :=
  Wrap (nat -> nat) (fun x => x + base).

Definition test_pack_fn_direct : nat :=
  let w := pack_fn_direct 10 in
  let f := unwrap w in
  f 5.
(** Expected: 15, but may crash with bad_any_cast *)

(** TEST 5: Pack a composed closure (let-bound, safe path). *)
Definition pack_composed (f : nat -> nat) (base : nat)
  : wrap (nat -> nat) :=
  let g := fun x => f x + base in
  Wrap (nat -> nat) g.

Definition test_pack_composed : nat :=
  let w := pack_composed (fun x => x * 2) 5 in
  let g := unwrap w in
  g 10.
(** Expected: 10 * 2 + 5 = 25 *)

(** TEST 6: Multiple wraps and unwraps. *)
Definition test_multi_wrap : nat :=
  let w1 := Wrap nat 10 in
  let w2 := Wrap nat 20 in
  unwrap w1 + unwrap w2.
(** Expected: 30 *)

(** TEST 7: Wrap a pair of nats. *)
Definition test_wrap_pair : nat :=
  let p := (3, 7) in
  let w := Wrap (nat * nat) p in
  let p2 := unwrap w in
  fst p2 + snd p2.
(** Expected: 10 *)

End MemSafetyProbe12.

Crane Extraction "mem_safety_probe12" MemSafetyProbe12.
