(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List Bool.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd External.Vector Monads.ITree Monads.IO Monads.STM.
From Corelib Require Import PrimInt63.

Import ListNotations.
Import MonadNotations.
Set Implicit Arguments.

(* ==== Key type requirements ==== *)

Module CHT.

Open Scope int63.

(* Assoc-list helpers parameterized by an equality function *)
Fixpoint assoc_lookup {K V} (eqb : K -> K -> bool) (k : K) (xs : list (K * V))
  : option V :=
  match xs with
  | [] => None
  | (k', v) :: tl => if eqb k k' then Some v else assoc_lookup eqb k tl
  end.

Fixpoint assoc_insert_or_replace {K V}
         (eqb : K -> K -> bool) (k : K) (v : V) (xs : list (K * V))
  : list (K * V) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: tl =>
      if eqb k k' then (k, v) :: tl
      else (k', v') :: assoc_insert_or_replace eqb k v tl
  end.

Fixpoint assoc_remove {K V}
         (eqb : K -> K -> bool) (k : K) (xs : list (K * V))
  : (option V * list (K * V)) :=
  match xs with
  | [] => (None, xs)
  | (k', v') :: tl =>
      if eqb k k'
      then (Some v', tl)
      else let q := assoc_remove eqb k tl in (fst q, (k', v') :: (snd q))
  end.

(* ==== Concurrent Hash Table (CHT) ==== *)

Record CHT (K V : Type) := {
  cht_eqb     : K -> K -> bool;
  cht_hash    : K -> int;
  cht_buckets : vector (TVar (list (K * V)));
  cht_nbuckets: int;                         (* cached, >= 1 *)
  cht_fallback: TVar (list (K * V))          (* first bucket as a total fallback *)
}.

(* Total bucket selection *)
Definition bucket_of {K V} (t : CHT K V) (k : K)
  :  STM (TVar (list (K * V))) :=
  let i := mod (t.(cht_hash) k) t.(cht_nbuckets) in
  getSTM t.(cht_buckets) i.

Section STM.
(* ---- Operations ---- *)

(* Get *)
Definition stm_get {K V} (t : CHT K V) (k : K) : STM (option V) :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  Ret (assoc_lookup t.(cht_eqb) k xs).

(* Put / upsert *)
Definition stm_put {K V} (t : CHT K V) (k : K) (v : V) : STM void :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret ghost.

(* Delete; returns previous value if any *)
Definition stm_delete {K V} (t : CHT K V) (k : K) : STM (option V) :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  let p := assoc_remove t.(cht_eqb) k xs in
  match fst p with
  | None => Ret (fst p)
  | _ =>
    writeTVar b (snd p) ;;
    Ret (fst p)
  end.

(* Update with a function of the old option; returns the new value *)
Definition stm_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : STM V :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  let ov := assoc_lookup t.(cht_eqb) k xs in
  let v  := f ov in
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret v.

(*
(* Blocking read until key appears *)
  Definition stm_wait {K V} (t : CHT K V) (k : K) : STM V :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  match assoc_lookup t.(cht_eqb) k xs with
  | Some v => Ret v
  | None   => r <- retry ;; Ret r
  end.

(* Try-get with default using orElse *)
Definition stm_get_or_bad {K V} (t : CHT K V) (k : K) (dflt : V) : STM V :=
  orElse (stm_wait t k) (Ret dflt).
*)

Definition stm_get_or {K V} (t : CHT K V) (k : K) (dflt : V) : STM V :=
  v <- stm_get t k ;;
  match v with
  | Some x => Ret x
  | None => Ret dflt
  end.

Definition max : int -> int -> int := fun a b =>
  if ltb a b then b else a.

End STM.

(* ---- IO wrappers (handy for extraction/run) ---- *)

(* Build N empty buckets *)
Definition mk_buckets {K V} (num : int) : IO (vector (TVar (list (K * V)))) :=
  buckets <- (emptyVec (TVar (list (K * V)))) ;;
  (fix f n := match n with
  | 0 => Ret buckets
  | S n' =>
    b <- atomically (newTVar ([] : list (K * V))) ;;
    push buckets b ;;
    f n'
  end) (nat_of_int num).

(* Create a new table with at least one bucket; stores eqb/hash in the record *)
Definition new_hash {K V}
           (eqb : K -> K -> bool) (hash : K -> int) (requested : int)
  : IO (CHT K V) :=
  let n := max requested 1 in
  bs <- mk_buckets (K:=K) (V:=V) n ;;
  empt <- isEmpty bs ;;
  if empt then
      fb <- atomically (newTVar ([] : list (K * V))) ;;
      v <- emptyVec (TVar (list (K * V))) ;;
      push v fb ;;
      Ret {| cht_eqb := eqb; cht_hash := hash;
                cht_buckets := v; cht_nbuckets := 1; cht_fallback := fb |}
  else
    b <- get bs 0 ;;
    Ret {| cht_eqb := eqb; cht_hash := hash;
                cht_buckets := bs; cht_nbuckets := n; cht_fallback := b |}.

Definition put  {K V} (t : CHT K V) (k : K) (v : V) : IO void :=
  atomically (stm_put t k v).

Definition get  {K V} (t : CHT K V) (k : K) : IO (option V) :=
  atomically (stm_get t k).

Definition hash_delete {K V} (t : CHT K V) (k : K) : IO (option V) :=
  atomically (stm_delete t k).

Definition hash_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : IO V :=
  atomically (stm_update t k f).

Definition get_or {K V} (t : CHT K V) (k : K) (dflt : V) : IO V :=
  atomically (stm_get_or t k dflt).

End CHT.

Crane Extract Inlined Constant CHT.max => "std::max(%a0, %a1)".
Crane Extraction TestCompile "hash" CHT.
