(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Mutable hash tables in local state ([ST]), after Haskell's
    [Data.HashTable.ST.Basic]: a table holds an [ST] reference to its
    [state], an [ST] array of buckets (separate chaining, see
    [HashTableDefs]) with its size and entry count.  A table doubles its
    buckets when it holds more entries than buckets.

    The store holds the buckets and the state, so a program's value types
    [V] need a [Code] for each; [store] is the [V] of a program whose only
    store is one kind of table.  The state mentions the array type, so [V]
    depends on the [Refs]: run such a program with [ST.run_dependent]. *)

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
From Crane Require Monads.ST.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** A table's mutable part: its bucket array, the array's size, and the
    number of entries. *)
Record state (R : ST.Refs) (K A : Type) : Type := mk_state {
  buckets : @ST.array R (bucket K A);
  capacity : nat;
  count : nat
}.
Arguments mk_state {R K A} buckets capacity count.
Arguments buckets {R K A} s.
Arguments capacity {R K A} s.
Arguments count {R K A} s.

(** A table from [K] to [A]: a reference to its state, whose state is
    replaced when the table grows. *)
Record t (R : ST.Refs) (K A : Type) : Type := mk_table {
  cell : @ST.ref R (state R K A)
}.
Arguments mk_table {R K A} cell.
Arguments cell {R K A} t.

(** The value types of a store holding tables from [K] to [A] only: code
    [0] holds buckets, every other code states. *)
Definition store (K A : Type) (R : ST.Refs) (c : nat) : Type :=
  match c with
  | O => bucket K A
  | S _ => state R K A
  end.

(** Buckets are stored at code [0] of [store]. *)
#[global] Instance code_bucket (K A : Type) (R : ST.Refs)
  : ST.Code (store K A R) (bucket K A) :=
  {| ST.code := 0; ST.code_ok := eq_refl |}.

(** States are stored at code [1] of [store]. *)
#[global] Instance code_state (K A : Type) (R : ST.Refs)
  : ST.Code (store K A R) (state R K A) :=
  {| ST.code := 1; ST.code_ok := eq_refl |}.

Section Operations.

  (** [K] and [A] come first: in C++ they are the leading template
      parameters, which a call to [new] spells out. *)
  Context {K A : Type} {R : ST.Refs} {V : nat -> Type} {E : Type -> Type}.
  Context `{ST.Event R V -< E} `{Hashable K}.
  Context {CB : ST.Code V (bucket K A)} {CS : ST.Code V (state R K A)}.

  (** An empty table of [n] buckets (at least one). *)
  Definition new_sized (n : nat) : itree E (t R K A) :=
    let cap := Nat.max n 1 in
    arr <- ST.new_array cap [];;
    r <- ST.new_ref (mk_state arr cap 0);;
    Ret (mk_table r).

  (** An empty table of [default_capacity] buckets. *)
  Definition new : itree E (t R K A) := new_sized default_capacity.

  (** The number of entries. *)
  Definition size (tbl : t R K A) : itree E nat :=
    s <- ST.read_ref (cell tbl);;
    Ret (count s).

  (** The value bound to [k], if any. *)
  Definition lookup (tbl : t R K A) (k : K) : itree E (option A) :=
    s <- ST.read_ref (cell tbl);;
    b <- ST.read_array (buckets s) (index k (capacity s));;
    Ret (bucket_find k b).

  (** Prepend [(k, v)] to its bucket in [arr], of [cap] buckets. *)
  Definition place (arr : @ST.array R (bucket K A)) (cap : nat) (k : K) (v : A)
    : itree E unit :=
    let i := index k cap in
    b <- ST.read_array arr i;;
    ST.write_array arr i ((k, v) :: b).

  (** Move every entry of [s] into an array of twice as many buckets, and
      make that the table's state. *)
  Definition grow (tbl : t R K A) (s : state R K A) : itree E unit :=
    let cap := 2 * capacity s in
    arr <- ST.new_array cap [];;
    bs <- ST.array_to_list (buckets s);;
    ST.for_each_with bs tt (fun _ b =>
      ST.for_each_with b tt (fun _ kv => place arr cap (fst kv) (snd kv)));;
    ST.write_ref (cell tbl) (mk_state arr cap (count s)).

  (** Record [n] entries in [s], growing once they outnumber the buckets. *)
  Definition set_count (tbl : t R K A) (s : state R K A) (n : nat) : itree E unit :=
    let s' := mk_state (buckets s) (capacity s) n in
    if Nat.ltb (capacity s) n then grow tbl s' else ST.write_ref (cell tbl) s'.

  (** Rebind [k] by [f]: [f] sees the current value, if any, and returns
      the new one, [None] to unbind.  One read and one write of [k]'s
      bucket, then the count is fixed. *)
  Definition alter (tbl : t R K A) (k : K) (f : option A -> option A) : itree E unit :=
    s <- ST.read_ref (cell tbl);;
    let i := index k (capacity s) in
    b <- ST.read_array (buckets s) i;;
    let old := bucket_find k b in
    let upd := f old in
    ST.write_array (buckets s) i (bucket_put k upd b);;
    if present old then
      if present upd then Ret tt else set_count tbl s (Nat.pred (count s))
    else
      if present upd then set_count tbl s (S (count s)) else Ret tt.

  (** Bind [k] to [v], replacing any earlier binding. *)
  Definition insert (tbl : t R K A) (k : K) (v : A) : itree E unit :=
    alter tbl k (fun _ => Some v).

  (** Unbind [k]; nothing happens if it is unbound. *)
  Definition delete (tbl : t R K A) (k : K) : itree E unit :=
    alter tbl k (fun _ => None).

  (** Fold a monadic step over the entries, in an unspecified order. *)
  Definition fold {B : Type} (f : B -> K -> A -> itree E B) (z : B) (tbl : t R K A)
    : itree E B :=
    s <- ST.read_ref (cell tbl);;
    bs <- ST.array_to_list (buckets s);;
    ST.for_each_with bs z (fun acc b =>
      ST.for_each_with b acc (fun acc' kv => f acc' (fst kv) (snd kv))).

  (** Run [f] on every entry, in an unspecified order. *)
  Definition iter (f : K -> A -> itree E unit) (tbl : t R K A) : itree E unit :=
    fold (fun _ k v => f k v) tt tbl.

  (** The entries, in an unspecified order. *)
  Definition to_list (tbl : t R K A) : itree E (list (K * A)) :=
    s <- ST.read_ref (cell tbl);;
    bs <- ST.array_to_list (buckets s);;
    Ret (concat bs).

  (** A new table holding [kvs]; a later binding of a key wins. *)
  Definition of_list (kvs : list (K * A)) : itree E (t R K A) :=
    tbl <- new;;
    ST.for_each_with kvs tt (fun _ kv => insert tbl (fst kv) (snd kv));;
    Ret tbl.

End Operations.

(** Codes have no C++ ([ST.Code] is skipped), so neither do these. *)
Crane Extract Skip code_bucket.
Crane Extract Skip code_state.


