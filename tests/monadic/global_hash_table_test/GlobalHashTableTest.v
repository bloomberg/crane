(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [GlobalHashTable]: every operation on tables from [nat] to [nat],
    including growth past the initial size, delete then reinsert, and
    [alter].  The programs are checked in the model ([Global.run]) and in
    C++. *)

From Stdlib Require Import Arith.PeanoNat List.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST Monads.Global Monads.GlobalHashTable.
From Crane Require Import
  Mapping.NatInt
  Monads.Error
  Monads.Indices
  Monads.ITree
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** Global state of the tables from [nat] to [nat]: their buckets and their
    states. *)
Notation E0 :=
  (GlobalHashTable.bucketE nat nat +' GlobalHashTable.stateE nat nat +' exceptE Err).

Section Programs.

  (** A table from [nat] to [nat]. *)
  Notation table := (GlobalHashTable.t nat nat).

  (** Binds [k] to [k * k] for every [k] of [ks]. *)
  Definition insert_squares (tbl : table) (ks : list nat) : itree E0 unit :=
    ST.for_each_with ks tt (fun _ k => GlobalHashTable.insert tbl k (k * k)).

  (** [n] squares in a table of two buckets, which grows past them: the
      size, two lookups and the entries. *)
  Definition growth (n : nat)
    : itree E0 (nat * option nat * option nat * list (nat * nat)) :=
    tbl <- GlobalHashTable.new_sized 2;;
    insert_squares tbl (seq 0 n);;
    s <- GlobalHashTable.size tbl;;
    a <- GlobalHashTable.lookup tbl 7;;
    b <- GlobalHashTable.lookup tbl n;;
    kvs <- GlobalHashTable.to_list tbl;;
    Ret (s, a, b, kvs).

  (** Delete [2], delete it again, then reinsert it: the lookups and sizes
      after each step. *)
  Definition delete_reinsert
    : itree E0 (option nat * nat * nat * option nat * nat) :=
    tbl <- GlobalHashTable.new;;
    insert_squares tbl [1; 2; 3];;
    GlobalHashTable.delete tbl 2;;
    gone <- GlobalHashTable.lookup tbl 2;;
    s1 <- GlobalHashTable.size tbl;;
    GlobalHashTable.delete tbl 2;;
    s2 <- GlobalHashTable.size tbl;;
    GlobalHashTable.insert tbl 2 100;;
    back <- GlobalHashTable.lookup tbl 2;;
    s3 <- GlobalHashTable.size tbl;;
    Ret (gone, s1, s2, back, s3).

  (** Counts one more occurrence of [k]. *)
  Definition bump (tbl : table) (k : nat) : itree E0 unit :=
    GlobalHashTable.alter tbl k (fun o =>
      match o with
      | Some c => Some (S c)
      | None => Some 1
      end).

  (** The occurrences of each element of [xs], counted by [alter]; then
      [alter] unbinds [0]. *)
  Definition counts (xs : list nat) : itree E0 (nat * list (nat * nat)) :=
    tbl <- GlobalHashTable.new_sized 1;;
    ST.for_each_with xs tt (fun _ x => bump tbl x);;
    GlobalHashTable.alter tbl 0 (fun _ => None);;
    s <- GlobalHashTable.size tbl;;
    kvs <- GlobalHashTable.to_list tbl;;
    Ret (s, kvs).

  (** [of_list] (a later binding wins), the sum of the values by [fold],
      and a copy with every value doubled by [iter]. *)
  Definition fold_iter (kvs : list (nat * nat))
    : itree E0 (nat * nat * list (nat * nat)) :=
    tbl <- GlobalHashTable.of_list kvs;;
    s <- GlobalHashTable.size tbl;;
    total <- GlobalHashTable.fold (fun acc _ v => Ret (acc + v)) 0 tbl;;
    copy <- GlobalHashTable.new;;
    GlobalHashTable.iter (fun k v => GlobalHashTable.insert copy k (2 * v)) tbl;;
    kvs' <- GlobalHashTable.to_list copy;;
    Ret (s, total, kvs').

End Programs.

(** Sorts entries by key, so that the model's results compare. *)
Definition sort_entries (kvs : list (nat * nat)) : list (nat * nat) :=
  fold_right (fun kv acc =>
    filter (fun e => Nat.ltb (fst e) (fst kv)) acc ++ kv
      :: filter (fun e => Nat.leb (fst kv) (fst e)) acc) [] kvs.

(** Runs a program in the model: the buckets' family, then the states'. *)
Definition run {X : Type} (t : itree E0 X) : itree (exceptE Err) X :=
  ITree.map (fun p => snd (snd p)) (Global.run (Global.run t)).

(** In the model: [growth 20] keeps every square through three doublings. *)
Example growth_model :
  burn 5000 (ITree.map (fun '(s, a, b, kvs) => (s, a, b, sort_entries kvs))
    (run (growth 20)))
  = Ret (20, Some 49, None, map (fun k => (k, k * k)) (seq 0 20)).
Proof. vm_compute. reflexivity. Qed.

(** In the model: [delete_reinsert]. *)
Example delete_reinsert_model :
  burn 5000 (run delete_reinsert)
  = Ret (None, 2, 2, Some 100, 3).
Proof. vm_compute. reflexivity. Qed.

(** In the model: [counts]. *)
Example counts_model :
  burn 5000 (ITree.map (fun '(s, kvs) => (s, sort_entries kvs))
    (run (counts [3; 0; 1; 3; 0; 3])))
  = Ret (2, [(1, 1); (3, 3)]).
Proof. vm_compute. reflexivity. Qed.

Module GlobalHashTableTest.
  (** [growth], in C++. *)
  Definition growth (n : nat) := growth n.
  (** [delete_reinsert], in C++. *)
  Definition delete_reinsert := delete_reinsert.
  (** [counts], in C++. *)
  Definition counts (xs : list nat) := counts xs.
  (** [fold_iter], in C++. *)
  Definition fold_iter (kvs : list (nat * nat)) := fold_iter kvs.
End GlobalHashTableTest.

Crane Extraction "global_hash_table_test" GlobalHashTableTest.
