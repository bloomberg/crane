(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Helper functions taking an ST array.  An array is a
    [std::shared_ptr<crane::array_storage<A>>], a mutable handle with a read
    view [std::span<const A>] and a writable view [std::span<A>], so each
    helper below is a function of its own:

    - [peek] only reads a cell: [std::span<const T>].
    - [bump] reads one cell and writes it back: [std::span<T>] (Read + Write
      joins to the writable view, which narrows to the read view for the
      read).
    - [ST.swap_array] (from [ST], not unfolded) likewise.
    - [outer -> middle -> ST.write_array]: the write reaches [outer] through
      [middle]; both take [std::span<T>].
    - [write_and_refill] writes a cell and calls [refill], a test-only
      operation that writes the whole array canonically ([WriteCanonical]):
      Write + WriteCanonical gives the canonical write-through form,
      [const std::shared_ptr<...>&].
    - [pick] returns one of its arrays, so it takes them by value, and so
      does [write_then_pick], which writes one and passes both to [pick]
      ([keep], which returns its array through [Ret], stays [const&]: see
      there); [regrow] (a test-only operation that reseats the handle,
      [Replace]) makes [regrow_then_write] take [std::shared_ptr<...>&].
    - Arrays of [nat] and of [bool]: [crane::array_storage<bool>] stores
      addressable [bool]s, so [flip] takes a [std::span<bool>] (never a span
      over a [std::vector<bool>]). *)

From Stdlib Require Import
  Arith.PeanoNat
  List
.
From Corelib Require PrimString.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST.
From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
.
From Crane Require Mapping.Descriptor.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module STArrayHelpers.

  Notation NatE := (ST.Event ST.cpp_refs (fun _ : nat => nat) +' exceptE Err).
  Notation BoolE := (ST.Event ST.cpp_refs (fun _ : nat => bool) +' exceptE Err).
  Notation NatArray := (@ST.array ST.cpp_refs nat).
  Notation BoolArray := (@ST.array ST.cpp_refs bool).

  (** Only reads a cell. *)
  Definition peek (arr : NatArray) (i : nat) : itree NatE nat :=
    ST.read_array arr i.

  (** Reads one cell and writes it back. *)
  Definition bump (arr : NatArray) (i : nat) : itree NatE unit :=
    v <- ST.read_array arr i;;
    ST.write_array arr i (S v).

  (** A write two calls deep. *)
  Definition middle (arr : NatArray) (i : nat) : itree NatE unit :=
    ST.write_array arr i 42.

  Definition outer (arr : NatArray) : itree NatE unit :=
    middle arr 0;;
    middle arr 2.

  (** Swaps the first and last cells: [ST.swap_array] is called, not unfolded. *)
  Definition swap_ends (arr : NatArray) (last : nat) : itree NatE unit :=
    ST.swap_array arr 0 last.

  (** Returns one of its arrays: it keeps them, so takes them by value. *)
  Definition pick (b : bool) (arr1 arr2 : NatArray) : NatArray :=
    if b then arr1 else arr2.

  (** Writes its first array and passes both to [pick], which keeps them:
      by value too. *)
  Definition write_then_pick (arr1 arr2 : NatArray) : itree NatE NatArray :=
    ST.write_array arr1 1 7;;
    Ret (pick true arr1 arr2).

  (** Returns its array through the monad's [Ret], a legacy mapping whose
      argument Crane takes to be only read: borrowed, and copied where it is
      returned. *)
  Definition keep (arr : NatArray) : itree NatE NatArray :=
    ST.write_array arr 1 7;;
    Ret arr.

  (** Reseats the handle to a fresh array of [n] zeros. *)
  Axiom regrow : NatArray -> nat -> itree NatE unit.

  (** Recursive helpers keep the view: a tail-recursive write loop takes the
      writable view, a non-tail-recursive read the read view. *)
  Fixpoint zero_from (arr : NatArray) (i n : nat) : itree NatE unit :=
    match n with
    | O => Ret tt
    | S m => ST.write_array arr i 0;; zero_from arr (S i) m
    end.

  Fixpoint sum_from (arr : NatArray) (i n : nat) : itree NatE nat :=
    match n with
    | O => Ret 0
    | S m =>
        x <- ST.read_array arr i;;
        r <- sum_from arr (S i) m;;
        Ret (x + r)
    end.

  (** Sets every cell to [v], through the canonical handle. *)
  Axiom refill : NatArray -> nat -> itree NatE unit.

  (** Writes a cell, then refills the array canonically. *)
  Definition write_and_refill (arr : NatArray) (v : nat) : itree NatE unit :=
    ST.write_array arr 0 v;;
    refill arr v.

  (** Replaces its array, then writes the new one. *)
  Definition regrow_then_write (arr : NatArray) (n : nat) : itree NatE unit :=
    regrow arr n;;
    ST.write_array arr 0 n.

  (** A [bool] array: reads one cell and writes its negation back. *)
  Definition flip (arr : BoolArray) (i : nat) : itree BoolE unit :=
    b <- ST.read_array arr i;;
    ST.write_array arr i (negb b).

  Definition helpers_list (xs : list nat) : list nat :=
    ST.run_cpp
      (arr <- ST.array_of_list xs;;
       bump arr 1;;
       outer arr;;
       swap_ends arr (length xs - 1);;
       ST.array_to_list arr).

  Definition keep_list (n : nat) : list nat * list nat :=
    ST.run_cpp
      (arr <- ST.new_array n 3;;
       other <- ST.new_array 2 4;;
       kept <- keep arr;;
       picked <- write_then_pick kept other;;
       ST.write_array picked 0 8;;
       elems <- ST.array_to_list arr;;
       others <- ST.array_to_list other;;
       Ret (elems, others)).

  Definition refill_list (n : nat) : nat * list nat :=
    ST.run_cpp
      (arr <- ST.new_array 3 1;;
       write_and_refill arr n;;
       first <- peek arr 0;;
       elems <- ST.array_to_list arr;;
       Ret (first, elems)).

  Definition loops_list (n : nat) : nat * list nat :=
    ST.run_cpp
      (arr <- ST.new_array n 2;;
       zero_from arr 1 2;;
       s <- sum_from arr 0 n;;
       elems <- ST.array_to_list arr;;
       Ret (s, elems)).

  Definition regrow_list (n : nat) : list nat :=
    ST.run_cpp
      (arr <- ST.new_array 2 5;;
       regrow_then_write arr n;;
       ST.array_to_list arr).

  Definition flip_list (bs : list bool) : list bool :=
    ST.run_cpp
      (arr <- ST.array_of_list bs;;
       flip arr 0;;
       flip arr 2;;
       ST.array_to_list arr).

  Definition bools_filled (n : nat) : bool * list bool :=
    ST.run_cpp
      (arr <- ST.new_array n false;;
       flip arr 1;;
       b <- ST.read_array arr 1;;
       elems <- ST.array_to_list arr;;
       Ret (b, elems)).

End STArrayHelpers.

Import Crane.Mapping.Descriptor.
From Corelib Require Import PrimString.
Open Scope pstring_scope.

#[export] Instance regrow_mapping : OperationMapping (Ref STArrayHelpers.regrow) :=
  {| operation_headers := ["memory"; "vector"];
     operation_cpp :=
       Expr "%arg(arr) = std::make_shared<crane::array_storage<uint64_t>>(%arg(n), 0)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := Replace |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance refill_mapping : OperationMapping (Ref STArrayHelpers.refill) :=
  {| operation_headers := ["algorithm"];
     operation_cpp := Expr "std::ranges::fill(*%arg(arr), %arg(v))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := WriteCanonical |};
          {| argument_name := "v"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "arr"; path_components := ["contents"] |} None] |}.


Crane Extraction "st_array_helpers" STArrayHelpers.
