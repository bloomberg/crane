(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Helper functions taking an ST array (docs/typed-mappings-design.md 13,
    24.6, 24.7).  An array is a [std::shared_ptr<crane::array_storage<A>>],
    a mutable handle with a read view [std::span<const A>] and a writable
    view [std::span<A>], so each helper below is a function of its own:

    - [peek] only reads a cell: [std::span<const T>].
    - [bump] reads one cell and writes it back: [std::span<T>] (Read + Write
      joins to the writable view, which narrows to the read view for the
      read).
    - [swapArray] (from [STMonad], not unfolded) likewise.
    - [outer -> middle -> writeArray]: the write reaches [outer] through
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

From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.STMonad
.
From Crane Require Mapping.Descriptor.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module StArrayHelpers.

  Notation NatE := (STEvent nat unit (fun _ : nat => nat) +' exceptE Err).
  Notation BoolE := (STEvent nat unit (fun _ : nat => bool) +' exceptE Err).
  Notation NatArray := (STArray nat unit nat).
  Notation BoolArray := (STArray nat unit bool).

  (** Only reads a cell. *)
  Definition peek (arr : NatArray) (i : nat) : itree NatE nat :=
    readArray (idx := 0) arr i.

  (** Reads one cell and writes it back. *)
  Definition bump (arr : NatArray) (i : nat) : itree NatE unit :=
    v <- readArray (idx := 0) arr i;;
    writeArray (idx := 0) arr i (S v).

  (** A write two calls deep. *)
  Definition middle (arr : NatArray) (i : nat) : itree NatE unit :=
    writeArray (idx := 0) arr i 42.

  Definition outer (arr : NatArray) : itree NatE unit :=
    middle arr 0;;
    middle arr 2.

  (** Swaps the first and last cells: [swapArray] is called, not unfolded. *)
  Definition swap_ends (arr : NatArray) (last : nat) : itree NatE unit :=
    swapArray (idx := 0) arr 0 last.

  (** Returns one of its arrays: it keeps them, so takes them by value. *)
  Definition pick (b : bool) (arr1 arr2 : NatArray) : NatArray :=
    if b then arr1 else arr2.

  (** Writes its first array and passes both to [pick], which keeps them:
      by value too. *)
  Definition write_then_pick (arr1 arr2 : NatArray) : itree NatE NatArray :=
    writeArray (idx := 0) arr1 1 7;;
    Ret (pick true arr1 arr2).

  (** Returns its array through the monad's [Ret], a legacy mapping whose
      argument Crane takes to be only read: borrowed, and copied where it is
      returned. *)
  Definition keep (arr : NatArray) : itree NatE NatArray :=
    writeArray (idx := 0) arr 1 7;;
    Ret arr.

  (** Reseats the handle to a fresh array of [n] zeros. *)
  Axiom regrow : NatArray -> nat -> itree NatE unit.

  (** Recursive helpers keep the view: a tail-recursive write loop takes the
      writable view, a non-tail-recursive read the read view. *)
  Fixpoint zero_from (arr : NatArray) (i n : nat) : itree NatE unit :=
    match n with
    | O => Ret tt
    | S m => writeArray (idx := 0) arr i 0;; zero_from arr (S i) m
    end.

  Fixpoint sum_from (arr : NatArray) (i n : nat) : itree NatE nat :=
    match n with
    | O => Ret 0
    | S m =>
        x <- readArray (idx := 0) arr i;;
        r <- sum_from arr (S i) m;;
        Ret (x + r)
    end.

  (** Sets every cell to [v], through the canonical handle. *)
  Axiom refill : NatArray -> nat -> itree NatE unit.

  (** Writes a cell, then refills the array canonically. *)
  Definition write_and_refill (arr : NatArray) (v : nat) : itree NatE unit :=
    writeArray (idx := 0) arr 0 v;;
    refill arr v.

  (** Replaces its array, then writes the new one. *)
  Definition regrow_then_write (arr : NatArray) (n : nat) : itree NatE unit :=
    regrow arr n;;
    writeArray (idx := 0) arr 0 n.

  (** A [bool] array: reads one cell and writes its negation back. *)
  Definition flip (arr : BoolArray) (i : nat) : itree BoolE unit :=
    b <- readArray (idx := 0) arr i;;
    writeArray (idx := 0) arr i (negb b).

  (** Runs an ST computation; [runST] only interprets into an [itree].
      Extracted as the identity. *)
  Axiom run_nat : forall (A : Type), itree NatE A -> A.
  Axiom run_bool : forall (A : Type), itree BoolE A -> A.

  Definition helpers_list (xs : list nat) : list nat :=
    run_nat (list nat)
      (arr <- newListArray 0 0 (length xs - 1) xs;;
       bump arr 1;;
       outer arr;;
       swap_ends arr (length xs - 1);;
       getElems (idx := 0) arr).

  Definition keep_list (n : nat) : list nat * list nat :=
    run_nat (list nat * list nat)
      (arr <- newArray 0 0 (n - 1) 3;;
       other <- newArray 0 0 1 4;;
       kept <- keep arr;;
       picked <- write_then_pick kept other;;
       writeArray (idx := 0) picked 0 8;;
       elems <- getElems (idx := 0) arr;;
       others <- getElems (idx := 0) other;;
       Ret (elems, others)).

  Definition refill_list (n : nat) : nat * list nat :=
    run_nat (nat * list nat)
      (arr <- newArray 0 0 2 1;;
       write_and_refill arr n;;
       first <- peek arr 0;;
       elems <- getElems (idx := 0) arr;;
       Ret (first, elems)).

  Definition loops_list (n : nat) : nat * list nat :=
    run_nat (nat * list nat)
      (arr <- newArray 0 0 (n - 1) 2;;
       zero_from arr 1 2;;
       s <- sum_from arr 0 n;;
       elems <- getElems (idx := 0) arr;;
       Ret (s, elems)).

  Definition regrow_list (n : nat) : list nat :=
    run_nat (list nat)
      (arr <- newArray 0 0 1 5;;
       regrow_then_write arr n;;
       getElems (idx := 0) arr).

  Definition flip_list (bs : list bool) : list bool :=
    run_bool (list bool)
      (arr <- newListArray 0 0 (length bs - 1) bs;;
       flip arr 0;;
       flip arr 2;;
       getElems (idx := 0) arr).

  Definition bools_filled (n : nat) : bool * list bool :=
    run_bool (bool * list bool)
      (arr <- newArray 0 0 (n - 1) false;;
       flip arr 1;;
       b <- readArray (idx := 0) arr 1;;
       elems <- getElems (idx := 0) arr;;
       Ret (b, elems)).

End StArrayHelpers.

Import Crane.Mapping.Descriptor.
From Corelib Require Import PrimString.
Open Scope pstring_scope.

#[export] Instance regrow_mapping : OperationMapping (Ref StArrayHelpers.regrow) :=
  {| operation_headers := ["memory"; "vector"];
     operation_cpp :=
       Expr "%arg(arr) = std::make_shared<crane::array_storage<uint64_t>>(%arg(n), 0)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := Replace |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance refill_mapping : OperationMapping (Ref StArrayHelpers.refill) :=
  {| operation_headers := ["algorithm"];
     operation_cpp := Expr "std::ranges::fill(*%arg(arr), %arg(v))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := WriteCanonical |};
          {| argument_name := "v"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "arr"; path_components := ["contents"] |} None] |}.

Crane Extract Inlined Constant StArrayHelpers.run_nat => "%a0".
Crane Extract Inlined Constant StArrayHelpers.run_bool => "%a0".

Crane Extraction "st_array_helpers" StArrayHelpers.
