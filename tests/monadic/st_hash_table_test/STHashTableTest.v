(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [STHashTable]: every operation on tables from [nat] to [nat], including
    growth past the initial size, delete then reinsert, and [alter].  The
    programs are checked in the model ([ST.run_dependent]) and in C++. *)

From Stdlib Require Import Arith.PeanoNat List.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST Monads.STHashTable.
From Crane Require Import
  Mapping.NatInt
  Monads.Error
  Monads.ITree
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Programs.

  (** The programs are polymorphic in [R], as [ST.run_dependent] requires. *)
  Context {R : ST.Refs}.
  (** The store holds tables from [nat] to [nat] only. *)
  Notation E0 := (ST.Event R (STHashTable.store nat nat R) +' exceptE Err).
  (** A table from [nat] to [nat]. *)
  Notation table := (STHashTable.t R nat nat).

  (** Binds [k] to [k * k] for every [k] of [ks]. *)
  Definition insert_squares (tbl : table) (ks : list nat) : itree E0 unit :=
    ST.for_each_with ks tt (fun _ k => STHashTable.insert tbl k (k * k)).

  (** [n] squares in a table of two buckets, which grows past them: the
      size, two lookups and the entries. *)
  Definition growth (n : nat)
    : itree E0 (nat * option nat * option nat * list (nat * nat)) :=
    tbl <- STHashTable.new_sized 2;;
    insert_squares tbl (seq 0 n);;
    s <- STHashTable.size tbl;;
    a <- STHashTable.lookup tbl 7;;
    b <- STHashTable.lookup tbl n;;
    kvs <- STHashTable.to_list tbl;;
    Ret (s, a, b, kvs).

  (** Delete [2], delete it again, then reinsert it: the lookups and sizes
      after each step. *)
  Definition delete_reinsert
    : itree E0 (option nat * nat * nat * option nat * nat) :=
    tbl <- STHashTable.new;;
    insert_squares tbl [1; 2; 3];;
    STHashTable.delete tbl 2;;
    gone <- STHashTable.lookup tbl 2;;
    s1 <- STHashTable.size tbl;;
    STHashTable.delete tbl 2;;
    s2 <- STHashTable.size tbl;;
    STHashTable.insert tbl 2 100;;
    back <- STHashTable.lookup tbl 2;;
    s3 <- STHashTable.size tbl;;
    Ret (gone, s1, s2, back, s3).

  (** Counts one more occurrence of [k]. *)
  Definition bump (tbl : table) (k : nat) : itree E0 unit :=
    STHashTable.alter tbl k (fun o =>
      match o with
      | Some c => Some (S c)
      | None => Some 1
      end).

  (** The occurrences of each element of [xs], counted by [alter]; then
      [alter] unbinds [0]. *)
  Definition counts (xs : list nat) : itree E0 (nat * list (nat * nat)) :=
    tbl <- STHashTable.new_sized 1;;
    ST.for_each_with xs tt (fun _ x => bump tbl x);;
    STHashTable.alter tbl 0 (fun _ => None);;
    s <- STHashTable.size tbl;;
    kvs <- STHashTable.to_list tbl;;
    Ret (s, kvs).

  (** [of_list] (a later binding wins), the sum of the values by [fold],
      and a copy with every value doubled by [iter]. *)
  Definition fold_iter (kvs : list (nat * nat))
    : itree E0 (nat * nat * list (nat * nat)) :=
    tbl <- STHashTable.of_list kvs;;
    s <- STHashTable.size tbl;;
    total <- STHashTable.fold (fun acc _ v => Ret (acc + v)) 0 tbl;;
    copy <- STHashTable.new;;
    STHashTable.iter (fun k v => STHashTable.insert copy k (2 * v)) tbl;;
    kvs' <- STHashTable.to_list copy;;
    Ret (s, total, kvs').

End Programs.

(** Sorts entries by key, so that the model's results compare. *)
Definition sort_entries (kvs : list (nat * nat)) : list (nat * nat) :=
  fold_right (fun kv acc =>
    filter (fun e => Nat.ltb (fst e) (fst kv)) acc ++ kv
      :: filter (fun e => Nat.leb (fst kv) (fst e)) acc) [] kvs.

(** In the model: [growth 20] keeps every square through three doublings. *)
Example growth_model :
  burn 5000 (ITree.map (fun '(s, a, b, kvs) => (s, a, b, sort_entries kvs))
    (ST.run_dependent (fun R => growth (R := R) 20)))
  = Ret (20, Some 49, None, map (fun k => (k, k * k)) (seq 0 20)).
Proof. vm_compute. reflexivity. Qed.

(** In the model: [delete_reinsert]. *)
Example delete_reinsert_model :
  burn 5000 (ST.run_dependent (fun R => delete_reinsert (R := R)))
  = Ret (None, 2, 2, Some 100, 3).
Proof. vm_compute. reflexivity. Qed.

(** In the model: [counts]. *)
Example counts_model :
  burn 5000 (ITree.map (fun '(s, kvs) => (s, sort_entries kvs))
    (ST.run_dependent (fun R => counts (R := R) [3; 0; 1; 3; 0; 3])))
  = Ret (2, [(1, 1); (3, 3)]).
Proof. vm_compute. reflexivity. Qed.

Module STHashTableTest.
  (** [growth], run in C++. *)
  Definition growth (n : nat) := ST.run_cpp (growth (R := ST.cpp_refs) n).
  (** [delete_reinsert], run in C++. *)
  Definition delete_reinsert := ST.run_cpp (delete_reinsert (R := ST.cpp_refs)).
  (** [counts], run in C++. *)
  Definition counts (xs : list nat) := ST.run_cpp (counts (R := ST.cpp_refs) xs).
  (** [fold_iter], run in C++. *)
  Definition fold_iter (kvs : list (nat * nat)) :=
    ST.run_cpp (fold_iter (R := ST.cpp_refs) kvs).
End STHashTableTest.

Crane Extraction "st_hash_table_test" STHashTableTest.
