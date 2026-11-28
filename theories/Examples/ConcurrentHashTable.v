(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrent hash table built on STM and vector effects.

   Flavor-independent implementation. Import a flavor file ([Monads.STM]
   or [Monads.STMBDE]) before extraction to supply the C++ inline customs.
   The [CHT.max] function needs a flavor-specific operation mapping, an
   [OperationMapping (Ref CHT.max)] calling [std::max] or [bsl::max].
*)
From Stdlib Require Import List Bool.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs Monads.STMDefs External.VectorDefs.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.

Import ListNotations.
Set Implicit Arguments.

(** An [int] as a [nat], to recurse on a bucket count; it has no Rocq
    definition, only its C++ mapping. *)
Axiom nat_of_int : int -> nat.
(** [nat_of_int i] is [i] converted modulo 2^32 to [uint32_t]. *)
#[export] Instance nat_of_int_mapping : OperationMapping (Ref nat_of_int) :=
  pure [] ["i"%pstring] (wrap Crane.Cpp.U32 (Crane.Cpp.Arg "i"%pstring)).

Module CHT.

Open Scope int63.

(** The value of the first pair whose key is [eqb]-equal to [k]. *)
Fixpoint assoc_lookup {K V} (eqb : K -> K -> bool) (k : K) (xs : list (K * V))
  : option V :=
  match xs with
  | [] => None
  | (k', v) :: tl => if eqb k k' then Some v else assoc_lookup eqb k tl
  end.

(** Replace the first binding of [k] in place, or append one. *)
Fixpoint assoc_insert_or_replace {K V}
         (eqb : K -> K -> bool) (k : K) (v : V) (xs : list (K * V))
  : list (K * V) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: tl =>
      if eqb k k' then (k, v) :: tl
      else (k', v') :: assoc_insert_or_replace eqb k v tl
  end.

(** Remove the first binding of [k], returning its value and the rest. *)
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

(** A hash table: a fixed vector of transactional buckets, each an
    association list, with the key equality and hash it was built with. *)
Record CHT (K V : Type) := {
  cht_eqb     : K -> K -> bool;
  cht_hash    : K -> int;
  cht_buckets : vector (TVar (list (K * V)));
  cht_nbuckets: int;                         (* cached, >= 1 *)
  cht_fallback: TVar (list (K * V))          (* first bucket as a total fallback *)
}.

(** The bucket of [k]: its hash modulo the bucket count. *)
Definition bucket_of {K V} (t : CHT K V) (k : K)
  :  itree stmE (TVar (list (K * V))) :=
  let i := mod (t.(cht_hash) k) t.(cht_nbuckets) in
  get_stm t.(cht_buckets) i.

Section STM.

(** The value bound to [k]. *)
Definition stm_get {K V} (t : CHT K V) (k : K) : itree stmE (option V) :=
  b <- bucket_of t k ;;
  xs <- read_tvar b ;;
  Ret (assoc_lookup t.(cht_eqb) k xs).

(** Bind [k] to [v], replacing any old binding. *)
Definition stm_put {K V} (t : CHT K V) (k : K) (v : V) : itree stmE unit :=
  b <- bucket_of t k ;;
  xs <- read_tvar b ;;
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  write_tvar b xs' ;;
  Ret tt.

(** Unbind [k], returning its old value; writes only if [k] was bound. *)
Definition stm_delete {K V} (t : CHT K V) (k : K) : itree stmE (option V) :=
  b <- bucket_of t k ;;
  xs <- read_tvar b ;;
  let p := assoc_remove t.(cht_eqb) k xs in
  match fst p with
  | None => Ret (fst p)
  | _ =>
    write_tvar b (snd p) ;;
    Ret (fst p)
  end.

(** Rebind [k] to [f] of its old value, returning the new one. *)
Definition stm_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : itree stmE V :=
  b <- bucket_of t k ;;
  xs <- read_tvar b ;;
  let ov := assoc_lookup t.(cht_eqb) k xs in
  let v  := f ov in
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  write_tvar b xs' ;;
  Ret v.

(** [k]'s value, or [dflt] where it is unbound. *)
Definition stm_get_or {K V} (t : CHT K V) (k : K) (dflt : V) : itree stmE V :=
  v <- stm_get t k ;;
  match v with
  | Some x => Ret x
  | None => Ret dflt
  end.

(** The larger [int]; a flavour maps it to [std::max] or [bsl::max]. *)
Definition max : int -> int -> int := fun a b =>
  if ltb a b then b else a.

End STM.

(** Vector and IO events: building a table needs both. *)
Definition vecIOE := vectorE +' ioE.
Crane Extract Skip vecIOE.

(** A vector of [num] buckets, each a fresh empty [TVar]. *)
Definition mk_buckets {K V} (num : int) : itree vecIOE (vector (TVar (list (K * V)))) :=
  buckets <- (empty_vector (TVar (list (K * V)))) ;;
  (fix f n := match n with
  | 0 => Ret buckets
  | S n' =>
    b <- atomically (new_tvar ([] : list (K * V))) ;;
    push buckets b ;;
    f n'
  end) (nat_of_int num).

(** A table with [max requested 1] buckets, storing [eqb] and [hash]. *)
Definition new_hash {K V}
           (eqb : K -> K -> bool) (hash : K -> int) (requested : int)
  : itree vecIOE (CHT K V) :=
  let n := max requested 1 in
  bs <- mk_buckets (K:=K) (V:=V) n ;;
  empt <- is_empty bs ;;
  if empt then
      fb <- atomically (new_tvar ([] : list (K * V))) ;;
      v <- empty_vector (TVar (list (K * V))) ;;
      push v fb ;;
      Ret {| cht_eqb := eqb; cht_hash := hash;
                cht_buckets := v; cht_nbuckets := 1; cht_fallback := fb |}
  else
    b <- get bs 0 ;;
    Ret {| cht_eqb := eqb; cht_hash := hash;
                cht_buckets := bs; cht_nbuckets := n; cht_fallback := b |}.

(** [stm_put] as its own transaction. *)
Definition put  {K V} (t : CHT K V) (k : K) (v : V) : itree ioE unit :=
  atomically (stm_put t k v).

(** [stm_get] as its own transaction. *)
Definition get  {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_get t k).

(** [stm_delete] as its own transaction. *)
Definition hash_delete {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_delete t k).

(** [stm_update] as its own transaction. *)
Definition hash_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : itree ioE V :=
  atomically (stm_update t k f).

(** [stm_get_or] as its own transaction. *)
Definition get_or {K V} (t : CHT K V) (k : K) (dflt : V) : itree ioE V :=
  atomically (stm_get_or t k dflt).

End CHT.
