(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** In-place quicksort on an ST array (Lomuto partition), next to the pure
    [quicksort_fun]. [StQuicksortProofs] shows that the two agree. *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
  List
.
From Stdlib Require PrimString.

From Equations Require Import Equations.

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

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Quicksort.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST : STRefClass T}.

  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  (** Lomuto partition of [arr[left..right]] around [arr[pivotIndex]];
      returns the final position of the pivot. *)
  Definition partition {E' : Type -> Type} `{STEvent T S V -< E'}
    (arr : STArray T S nat) (arr_idx left right pivotIndex : T) : itree E' T :=
    pivotValue <- readArray (idx := arr_idx) arr pivotIndex;;
    swapArray (idx := arr_idx) arr pivotIndex right;;
    storeIndex <- for_each_with (range left (sub right (suc zero))) left
      (fun storeIndex i =>
        val <- readArray (idx := arr_idx) arr i;;
        if Nat.leb val pivotValue
        then swapArray (idx := arr_idx) arr i storeIndex;;
             Ret (suc storeIndex)
        else Ret storeIndex);;
    swapArray (idx := arr_idx) arr storeIndex right;;
    Ret storeIndex.

  (** The recursion is not structural (the pivot comes out of an effectful
      [partition]), so it runs on [fuel]: a segment of [n] elements needs
      [n] steps. *)
  Fixpoint quicksort_ST (fuel : nat) (arr : STArray T S nat) (arr_idx l r : T)
    : itree E0 unit :=
    match fuel with
    | O => Ret tt
    | Datatypes.S fuel' =>
      if Nat.ltb (toNat l) (toNat r) then
        let leftn := toNat l in
        let rightn := toNat r in
        let pivotIndexn := leftn + ((rightn - leftn) / 2) in
        newPivot <- partition arr arr_idx l r (fromNat pivotIndexn);;
        quicksort_ST fuel' arr arr_idx l (fromNat (toNat newPivot - 1));;
        quicksort_ST fuel' arr arr_idx (fromNat (toNat newPivot + 1)) r
      else Ret tt
    end.

  Definition quicksort_ST_list (xs : list nat) : itree E0 (list nat) :=
    match xs with
    | [] => Ret []
    | _ :: _ =>
      let lastIndex := fromNat (length xs - 1) in
      arr <- newListArray zero zero lastIndex xs;;
      quicksort_ST (length xs) arr zero zero lastIndex;;
      getElems (idx := zero) arr
    end.

End Quicksort.

Lemma filter_length {A} (f : A -> bool) (l : list A) :
  length (List.filter f l) <= length l.
Proof. induction l; simpl; [lia | destruct (f a); simpl; lia]. Qed.

Equations? quicksort_fun (l : list nat) : list nat by wf (length l) lt :=
  quicksort_fun [] => [];
  quicksort_fun (p :: xs) =>
    quicksort_fun (List.filter (fun x => Nat.ltb x p) xs)
      ++ [p] ++
    quicksort_fun (List.filter (fun x => Nat.leb p x) xs).
Proof.
  - specialize (filter_length (fun x => Nat.ltb x p) xs). simpl. lia.
  - specialize (filter_length (fun x => Nat.leb p x) xs). simpl. lia.
Defined.

Module StQuicksort.
  (* The index instances are unfolded so that they are extracted here. *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.

  Transparent quicksort_fun.
  Definition quicksort_fun := Eval unfold quicksort_fun in (@quicksort_fun).
  Definition quicksort_ST_mine :=
    Eval unfold quicksort_ST_list in
      (@quicksort_ST_list nat unit Nat.le nat_idx nat_stref).

  Definition nth := Eval unfold List.nth in (@List.nth nat).

  Import PrimString.

  Fixpoint list_to_string_helper (l : list nat) : PrimString.string :=
    match l with
    | nil => ""
    | x :: xs => PrimString.cat (string_of_nat x) (PrimString.cat ", " (list_to_string_helper xs))
    end.

  Definition list_to_string (l : list nat) : PrimString.string :=
    PrimString.cat "[ " (PrimString.cat (list_to_string_helper l) " ]").

  (** Turns the ST computation into its result; [runST] only interprets into
      [itree void1 A]. Extracted as the identity. *)
  Axiom runST' : forall (A : Type), itree (STEvent nat unit (fun _ : nat => nat) +' exceptE Err) A -> A.

  Definition input_lst1 := [212498; 127; 5981; 2749812; 74879; 126; 4; 51; 2412; 10645].

  Definition test_quicksort_ST (_ : unit) : PrimString.string :=
    runST' PrimString.string
      (out <- quicksort_ST_mine input_lst1;;
       Ret (list_to_string out)).

  Definition test_quicksort_fun (_ : unit) : PrimString.string :=
    list_to_string (quicksort_fun input_lst1).
End StQuicksort.

Set Crane Loopify.
(** The two recursive calls stay C++ recursion, as deep as the sort:
    Loopify cannot yet lower two self-calls in sequence at [itree E unit]
    (tests/wip/itree_two_self_calls). *)
Crane NoLoopify quicksort_ST.
Crane Extract Inlined Constant StQuicksort.runST' => "%a0".

Crane Extraction "st_quicksort" StQuicksort.

Crane Benchmark
  StQuicksort.test_quicksort_fun,
  StQuicksort.test_quicksort_ST
On C++ With "".
