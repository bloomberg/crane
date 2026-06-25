From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

(** Memory safety probe: type-indexed inductives and erased fields.

    When an inductive is indexed by a type (not parameterized), Crane
    erases the index to std::any. Accessing fields stored as std::any
    requires any_cast, which creates a temporary. If a reference to
    the any_cast result is used after the temporary dies, we get UB.

    This probes patterns where:
    1. A type-indexed container stores values as std::any
    2. Pattern matching extracts the any value
    3. The extracted value is used in a context where its lifetime
       may have ended *)

Module ErasedFieldDangle.

(** A container indexed by the element type — not parameterized.
    The index is erased to std::any in C++. *)
Inductive box : Set -> Type :=
  | MkBox : forall (A : Set), A -> box A.

(** Extract the value from a box. In Rocq this is safe.
    In C++, the any_cast result is a temporary. *)
Definition unbox {A : Set} (b : box A) : A :=
  match b with
  | MkBox _ x => x
  end.

(** Nested boxes: box of box *)
Definition nested_box : box (nat * nat) :=
  MkBox _ (42, 58).

Definition test_unbox_nested : nat :=
  let p := unbox nested_box in
  fst p + snd p.

(** Use unboxed value in a computation *)
Definition test_unbox_compute : nat :=
  let x := unbox (MkBox _ 10) in
  let y := unbox (MkBox _ 20) in
  x + y.

(** Chain unbox through multiple let bindings *)
Definition test_chain_unbox : nat :=
  let b1 := MkBox _ 5 in
  let b2 := MkBox _ (unbox b1 + 10) in
  let b3 := MkBox _ (unbox b2 + 20) in
  unbox b3.

(** Pass unboxed value to a higher-order function *)
Definition test_hof_unbox : nat :=
  let b := MkBox _ (fun x : nat => x * 2) in
  let f := unbox b in
  f 21.

(** Existential container: hide the type *)
Inductive exists_box : Type :=
  | Pack : forall (A : Set), A -> (A -> nat) -> exists_box.

Definition run_exists (e : exists_box) : nat :=
  match e with
  | Pack _ x f => f x
  end.

Definition test_exists : nat :=
  let e := Pack _ 7 (fun x => x * x) in
  run_exists e.

End ErasedFieldDangle.

Crane Extraction "erased_field_dangle" ErasedFieldDangle.
