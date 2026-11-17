(** Workloads for measuring the C++ Crane generates: persistent trees, list
    pipelines, an interpreter, closures and a balanced map from the standard
    library.  Each entry point folds its result into one number. *)
From Stdlib Require Import List PeanoNat FMapAVL OrderedTypeEx.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.
Import ListNotations.

Module GbLists.

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

(** List pipelines and a merge sort with fuel. *)
Fixpoint merge (l1 : list nat) : list nat -> list nat :=
  fix merge_aux (l2 : list nat) :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | a1 :: l1', a2 :: l2' =>
      if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
    end.

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | a :: b :: rest => let (x, y) := split rest in (a :: x, b :: y)
  | _ => (l, [])
  end.

Fixpoint msort (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S f =>
    match l with
    | [] | [_] => l
    | _ => let (x, y) := split l in merge (msort f x) (msort f y)
    end
  end.

Fixpoint checksum (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: r => checksum r ((acc * 31 + x) mod m_sum)
  end.

Definition lists (n rounds : nat) : nat :=
  fold_left
    (fun acc i =>
       let l := map (fun x => x mod m_val + i) (randoms n (i + 1)) in
       let l := filter (fun x => negb (x mod 3 =? 0)) l in
       let s := msort 64 (l ++ rev l) in
       checksum s acc + fold_right (fun x a => x + a) 0 l)
    (seq 0 rounds) 0.

End GbLists.

Crane Extract Inlined Constant GbLists.m_lcg => "UINT64_C(65537)".
Crane Extract Inlined Constant GbLists.m_sum => "UINT64_C(65535)".
Crane Extract Inlined Constant GbLists.m_clo => "UINT64_C(4093)".
Crane Extract Inlined Constant GbLists.m_val => "UINT64_C(4096)".
Crane Extract Inlined Constant GbLists.m_key => "UINT64_C(4000)".
Crane Extract Inlined Constant GbLists.m_map => "UINT64_C(1000)".
Crane Extract Inlined Constant GbLists.fuel_big => "UINT64_C(100000000)".
Set Crane Loopify.
Crane Extraction "gb_lists" GbLists.
