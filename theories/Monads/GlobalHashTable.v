(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Mutable hash tables in global state ([Global]), after Haskell's
    [Data.HashTable.IO]: the tables of [STHashTable] over [Global]'s
    references and arrays.  A table holds a reference to its [state], an
    array of buckets (separate chaining, see [HashTableDefs]) with its
    size and entry count, and doubles its buckets when it holds more
    entries than buckets.

    The buckets and the states are two families of global state, each
    with one value type: a program using tables from [K] to [A] triggers
    [bucketE K A] and [stateE K A]. *)

From Stdlib Require Import
  Arith.PeanoNat
  List
.

From ITree Require Import ITree.

From Crane Require Import
  Extraction
  Monads.ITree
  Monads.HashTableDefs
.
From Crane Require Monads.Global Monads.ST.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** A table's mutable part: its bucket array, the array's size, and the
    number of entries. *)
Record state (K A : Type) : Type := mk_state {
  buckets : Global.array nat (bucket K A);
  capacity : nat;
  count : nat
}.
Arguments mk_state {K A} buckets capacity count.
Arguments buckets {K A} s.
Arguments capacity {K A} s.
Arguments count {K A} s.

(** A table from [K] to [A]: a reference to its state, whose state is
    replaced when the table grows. *)
Record t (K A : Type) : Type := mk_table {
  cell : Global.ref (state K A)
}.
Arguments mk_table {K A} cell.
Arguments cell {K A} t.

(** The global state of the buckets: a family of its own whose every
    index holds buckets, so that each family has one value type. *)
Notation bucketE K A := (Global.Event nat (fun _ : nat => bucket K A)).

(** The global state of the tables' states. *)
Notation stateE K A := (Global.Event nat (fun _ : nat => state K A)).

Section Operations.

  Context {K A : Type} {E : Type -> Type}.
  Context `{bucketE K A -< E} `{stateE K A -< E} `{Hashable K}.

  (** The value types of the two families. *)
  Notation BV := (fun _ : nat => bucket K A).
  Notation SV := (fun _ : nat => state K A).

  (** An empty table of [n] buckets (at least one). *)
  Definition new_sized (n : nat) : itree E (t K A) :=
    let cap := Nat.max n 1 in
    arr <- Global.new_array (V := BV) 0 cap [];;
    r <- Global.new_ref (V := SV) 0 (mk_state arr cap 0);;
    Ret (mk_table r).

  (** An empty table of [default_capacity] buckets. *)
  Definition new : itree E (t K A) := new_sized default_capacity.

  (** The number of entries. *)
  Definition size (tbl : t K A) : itree E nat :=
    s <- Global.read_ref (V := SV) (idx := 0) (cell tbl);;
    Ret (count s).

  (** The value bound to [k], if any. *)
  Definition lookup (tbl : t K A) (k : K) : itree E (option A) :=
    s <- Global.read_ref (V := SV) (idx := 0) (cell tbl);;
    b <- Global.read_array (V := BV) (idx := 0) (buckets s) (index k (capacity s));;
    Ret (bucket_find k b).

  (** Prepend [(k, v)] to its bucket in [arr], of [cap] buckets. *)
  Definition place (arr : Global.array nat (bucket K A)) (cap : nat) (k : K) (v : A)
    : itree E unit :=
    let i := index k cap in
    b <- Global.read_array (V := BV) (idx := 0) arr i;;
    Global.write_array (V := BV) (idx := 0) arr i ((k, v) :: b).

  (** Move every entry of [s] into an array of twice as many buckets, and
      make that the table's state. *)
  Definition grow (tbl : t K A) (s : state K A) : itree E unit :=
    let cap := 2 * capacity s in
    arr <- Global.new_array (V := BV) 0 cap [];;
    bs <- Global.array_to_list (V := BV) (idx := 0) (buckets s);;
    ST.for_each_with bs tt (fun _ b =>
      ST.for_each_with b tt (fun _ kv => place arr cap (fst kv) (snd kv)));;
    Global.write_ref (V := SV) (idx := 0) (cell tbl) (mk_state arr cap (count s)).

  (** Record [n] entries in [s], growing once they outnumber the buckets. *)
  Definition set_count (tbl : t K A) (s : state K A) (n : nat) : itree E unit :=
    let s' := mk_state (buckets s) (capacity s) n in
    if Nat.ltb (capacity s) n then grow tbl s' else Global.write_ref (V := SV) (idx := 0) (cell tbl) s'.

  (** Rebind [k] by [f]: [f] sees the current value, if any, and returns
      the new one, [None] to unbind.  One read and one write of [k]'s
      bucket, then the count is fixed. *)
  Definition alter (tbl : t K A) (k : K) (f : option A -> option A) : itree E unit :=
    s <- Global.read_ref (V := SV) (idx := 0) (cell tbl);;
    let i := index k (capacity s) in
    b <- Global.read_array (V := BV) (idx := 0) (buckets s) i;;
    let old := bucket_find k b in
    let upd := f old in
    Global.write_array (V := BV) (idx := 0) (buckets s) i (bucket_put k upd b);;
    if present old then
      if present upd then Ret tt else set_count tbl s (Nat.pred (count s))
    else
      if present upd then set_count tbl s (S (count s)) else Ret tt.

  (** Bind [k] to [v], replacing any earlier binding. *)
  Definition insert (tbl : t K A) (k : K) (v : A) : itree E unit :=
    alter tbl k (fun _ => Some v).

  (** Unbind [k]; nothing happens if it is unbound. *)
  Definition delete (tbl : t K A) (k : K) : itree E unit :=
    alter tbl k (fun _ => None).

  (** Fold a monadic step over the entries, in an unspecified order. *)
  Definition fold {B : Type} (f : B -> K -> A -> itree E B) (z : B) (tbl : t K A)
    : itree E B :=
    s <- Global.read_ref (V := SV) (idx := 0) (cell tbl);;
    bs <- Global.array_to_list (V := BV) (idx := 0) (buckets s);;
    ST.for_each_with bs z (fun acc b =>
      ST.for_each_with b acc (fun acc' kv => f acc' (fst kv) (snd kv))).

  (** Run [f] on every entry, in an unspecified order. *)
  Definition iter (f : K -> A -> itree E unit) (tbl : t K A) : itree E unit :=
    fold (fun _ k v => f k v) tt tbl.

  (** The entries, in an unspecified order. *)
  Definition to_list (tbl : t K A) : itree E (list (K * A)) :=
    s <- Global.read_ref (V := SV) (idx := 0) (cell tbl);;
    bs <- Global.array_to_list (V := BV) (idx := 0) (buckets s);;
    Ret (concat bs).

  (** A new table holding [kvs]; a later binding of a key wins. *)
  Definition of_list (kvs : list (K * A)) : itree E (t K A) :=
    tbl <- new;;
    ST.for_each_with kvs tt (fun _ kv => insert tbl (fst kv) (snd kv));;
    Ret tbl.

End Operations.
