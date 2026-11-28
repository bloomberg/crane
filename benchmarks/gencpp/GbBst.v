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

Module GbBst.

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

(** Unbalanced search trees: insertion and folds are non-tail recursive. *)
Inductive tree := Leaf | Node (l : tree) (k : nat) (r : tree).

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l k r =>
    if x <? k then Node (insert x l) k r
    else if k <? x then Node l k (insert x r)
    else t
  end.

Fixpoint tsum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l k r => tsum l + k + tsum r
  end.

Fixpoint tmap (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k r => Node (tmap f l) (f k) (tmap f r)
  end.

Fixpoint to_list (t : tree) (acc : list nat) : list nat :=
  match t with
  | Leaf => acc
  | Node l k r => to_list l (k :: to_list r acc)
  end.

Definition bst (n rounds : nat) : nat :=
  let t := fold_left (fun t x => insert x t) (randoms n 7) Leaf in
  fold_left (fun acc i => acc + tsum (tmap (fun k => k + i) t)) (seq 0 rounds) 0
  + length (to_list t []).

End GbBst.

#[global] Instance m_lcg_mapping : OperationMapping (Ref (@GbBst.m_lcg)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65537)")).
#[global] Instance m_sum_mapping : OperationMapping (Ref (@GbBst.m_sum)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65535)")).
#[global] Instance m_clo_mapping : OperationMapping (Ref (@GbBst.m_clo)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4093)")).
#[global] Instance m_val_mapping : OperationMapping (Ref (@GbBst.m_val)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4096)")).
#[global] Instance m_key_mapping : OperationMapping (Ref (@GbBst.m_key)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4000)")).
#[global] Instance m_map_mapping : OperationMapping (Ref (@GbBst.m_map)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(1000)")).
#[global] Instance fuel_big_mapping : OperationMapping (Ref (@GbBst.fuel_big)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(100000000)")).
Set Crane Loopify.
Crane Extraction "gb_bst" GbBst.
