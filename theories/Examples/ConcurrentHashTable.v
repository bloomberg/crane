(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrent hash table built on STM and vector effects.

   Flavor-independent implementation. Import a flavor file ([Monads.STM]
   or [Monads.STMBDE]) before extraction to supply the C++ inline customs.
   The [CHT.max] function needs a flavor-specific inline custom:
   - Std: [Crane Extract Inlined Constant CHT.max => "std::max(%a0, %a1)".]
   - BDE: [Crane Extract Inlined Constant CHT.max => "bsl::max(%a0, %a1)".]
*)
From Stdlib Require Import List Bool.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs Monads.STMDefs External.VectorDefs.
From Corelib Require Import PrimInt63.

Import ListNotations.
Set Implicit Arguments.

Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "static_cast<unsigned int>(%a0)".

Module CHT.

Open Scope int63.

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

Record CHT (K V : Type) := {
  cht_eqb     : K -> K -> bool;
  cht_hash    : K -> int;
  cht_buckets : vector (TVar (list (K * V)));
  cht_nbuckets: int;                         (* cached, >= 1 *)
  cht_fallback: TVar (list (K * V))          (* first bucket as a total fallback *)
}.

(* Total bucket selection *)
Definition bucket_of {K V} (t : CHT K V) (k : K)
  :  itree stmE (TVar (list (K * V))) :=
  let i := mod (t.(cht_hash) k) t.(cht_nbuckets) in
  getSTM t.(cht_buckets) i.

Section STM.

(* Get *)
Definition stm_get {K V} (t : CHT K V) (k : K) : itree stmE (option V) :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  Ret (assoc_lookup t.(cht_eqb) k xs).

(* Put / upsert *)
Definition stm_put {K V} (t : CHT K V) (k : K) (v : V) : itree stmE unit :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret tt.

(* Delete; returns previous value if any *)
Definition stm_delete {K V} (t : CHT K V) (k : K) : itree stmE (option V) :=
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
           (t : CHT K V) (k : K) (f : option V -> V) : itree stmE V :=
  b <- bucket_of t k ;;
  xs <- readTVar b ;;
  let ov := assoc_lookup t.(cht_eqb) k xs in
  let v  := f ov in
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret v.

Definition stm_get_or {K V} (t : CHT K V) (k : K) (dflt : V) : itree stmE V :=
  v <- stm_get t k ;;
  match v with
  | Some x => Ret x
  | None => Ret dflt
  end.

Definition max : int -> int -> int := fun a b =>
  if ltb a b then b else a.

End STM.

Definition vecIOE := vectorE +' ioE.
Crane Extract Skip vecIOE.

(* Build N empty buckets *)
Definition mk_buckets {K V} (num : int) : itree vecIOE (vector (TVar (list (K * V)))) :=
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
  : itree vecIOE (CHT K V) :=
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

Definition put  {K V} (t : CHT K V) (k : K) (v : V) : itree ioE unit :=
  atomically (stm_put t k v).

Definition get  {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_get t k).

Definition hash_delete {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_delete t k).

Definition hash_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : itree ioE V :=
  atomically (stm_update t k f).

Definition get_or {K V} (t : CHT K V) (k : K) (dflt : V) : itree ioE V :=
  atomically (stm_get_or t k dflt).

End CHT.
