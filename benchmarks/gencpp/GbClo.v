(** Workloads for measuring the C++ Crane generates: persistent trees, list
    pipelines, an interpreter, closures and a balanced map from the standard
    library.  Each entry point folds its result into one number. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Stdlib Require Import List PeanoNat FMapAVL OrderedTypeEx.
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
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

#[global] Instance m_lcg_mapping : OperationMapping (Ref (@GbClo.m_lcg)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65537)")).
#[global] Instance m_sum_mapping : OperationMapping (Ref (@GbClo.m_sum)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65535)")).
#[global] Instance m_clo_mapping : OperationMapping (Ref (@GbClo.m_clo)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4093)")).
#[global] Instance m_val_mapping : OperationMapping (Ref (@GbClo.m_val)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4096)")).
#[global] Instance m_key_mapping : OperationMapping (Ref (@GbClo.m_key)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4000)")).
#[global] Instance m_map_mapping : OperationMapping (Ref (@GbClo.m_map)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(1000)")).
#[global] Instance fuel_big_mapping : OperationMapping (Ref (@GbClo.fuel_big)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(100000000)")).
Set Crane Loopify.
Crane Extraction "gb_clo" GbClo.
