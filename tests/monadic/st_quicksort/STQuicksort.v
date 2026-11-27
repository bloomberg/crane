(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** In-place quicksort on an ST array (Lomuto partition), next to the pure
    [quicksort_fun]. [STQuicksortProofs] shows that the two agree. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Wf_nat
  Lia
  List
.
From Stdlib Require PrimString.

From Equations Require Import Equations.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST.
From Crane Require Import
  Mapping.NatInt
  Monads.Error
  Monads.ITree
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Quicksort.

  Context {R : ST.Refs}.
  Notation V := (fun _ : nat => nat).
  Notation E0 := (ST.Event R V +' exceptE Err).

  (** The Lomuto scan of [arr[i..hi-1]] against the pivot value [pv]: an
      element [<= pv] is swapped to [s], the next free slot of the small
      region [lo..s-1].  Returns the final [s], with its bounds.  It
      recurses on the accessibility of [hi - i], which is erased; the
      proofs are left as holes and closed below the definition. *)
  #[refine] Fixpoint lomuto_scan {E' : Type -> Type} `{ST.Event R V -< E'}
    (arr : ST.array nat) (pv lo hi i s : nat)
    (Hs : lo <= s <= i) (Hi : i <= hi) (acc : Acc lt (hi - i)) {struct acc}
    : itree E' {p : nat | lo <= p <= hi} :=
    match Sumbool.sumbool_of_bool (Nat.ltb i hi) with
    | left Hlt =>
      v <- ST.read_array (E := E') (V := V) arr i;;
      if Nat.leb v pv
      then ST.swap_array (E := E') (V := V) arr i s;;
           @lomuto_scan E' _ arr pv lo hi (Datatypes.S i) (Datatypes.S s) _ _
             (@Acc_inv _ _ _ acc (hi - Datatypes.S i) _)
      else @lomuto_scan E' _ arr pv lo hi (Datatypes.S i) s _ _
             (@Acc_inv _ _ _ acc (hi - Datatypes.S i) _)
    | right Hge => Ret (exist (fun p => lo <= p <= hi) s _)
    end.
  Proof. all: first [ apply Nat.ltb_lt in Hlt | apply Nat.ltb_ge in Hge ]; lia. Defined.

  (** Lomuto partition of [arr[lo..hi]] around [arr[pividx]]; returns the
      final position of the pivot, within [lo..hi]. *)
  #[refine] Definition partition {E' : Type -> Type} `{ST.Event R V -< E'}
    (arr : ST.array nat) (lo hi pividx : nat) (Hlo : lo <= hi)
    : itree E' {p : nat | lo <= p <= hi} :=
    pv <- ST.read_array (E := E') (V := V) arr pividx;;
    ST.swap_array (E := E') (V := V) arr pividx hi;;
    p <- @lomuto_scan E' _ arr pv lo hi lo lo _ Hlo (lt_wf (hi - lo));;
    ST.swap_array (E := E') (V := V) arr (proj1_sig p) hi;;
    Ret p.
  Proof. lia. Defined.

  (** In-place quicksort of [arr[lo..hi]].  The pivot comes out of an
      effectful [partition], so the recursion is not structural: it is on
      the accessibility of [hi - lo], which [partition]'s bounds decrease.
      The proofs are erased; no counter runs. *)
  #[refine] Fixpoint quicksort_ST {E' : Type -> Type} `{ST.Event R V -< E'}
    (arr : ST.array nat) (lo hi : nat) (acc : Acc lt (hi - lo)) {struct acc} : itree E' unit :=
    match Sumbool.sumbool_of_bool (Nat.ltb lo hi) with
    | left Hlt =>
      p <- @partition E' _ arr lo hi (lo + (hi - lo) / 2) _;;
      @quicksort_ST E' _ arr lo (proj1_sig p - 1)
        (@Acc_inv _ _ _ acc (proj1_sig p - 1 - lo) _);;
      @quicksort_ST E' _ arr (proj1_sig p + 1) hi
        (@Acc_inv _ _ _ acc (hi - (proj1_sig p + 1)) _)
    | right _ => Ret tt
    end.
  Proof. all: apply Nat.ltb_lt in Hlt; try (destruct p as [q Hq]; cbn [proj1_sig]); lia. Defined.

  (** [Acc_intro_generator] puts [2^10] layers of [Acc_intro] in front of
      [lt_wf], so that the sort also computes in Rocq. *)
  Definition quicksort_ST_list (xs : list nat) : itree E0 (list nat) :=
    match xs with
    | [] => Ret []
    | _ :: _ =>
      arr <- ST.array_of_list (E := E0) (V := V) xs;;
      quicksort_ST arr 0 (length xs - 1) (Acc_intro_generator 10 lt_wf _);;
      ST.array_to_list (E := E0) (V := V) arr
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

Module STQuicksort.
  Transparent quicksort_fun.
  Definition quicksort_fun := Eval unfold quicksort_fun in (@quicksort_fun).
  Definition quicksort_ST_mine :=
    Eval unfold quicksort_ST_list in
      (@quicksort_ST_list ST.cpp_refs).

  Definition nth := Eval unfold List.nth in (@List.nth nat).

  Import PrimString.

  Fixpoint list_to_string_helper (l : list nat) : PrimString.string :=
    match l with
    | nil => ""
    | x :: xs => PrimString.cat (string_of_nat x) (PrimString.cat ", " (list_to_string_helper xs))
    end.

  Definition list_to_string (l : list nat) : PrimString.string :=
    PrimString.cat "[ " (PrimString.cat (list_to_string_helper l) " ]").

  Definition input_lst1 := [212498; 127; 5981; 2749812; 74879; 126; 4; 51; 2412; 10645].

  Definition test_quicksort_ST (_ : unit) : PrimString.string :=
    ST.run_cpp
      (out <- quicksort_ST_mine input_lst1;;
       Ret (list_to_string out)).

  Definition test_quicksort_fun (_ : unit) : PrimString.string :=
    list_to_string (quicksort_fun input_lst1).
End STQuicksort.

Set Crane Loopify.
(** The two recursive calls stay C++ recursion, as deep as the sort:
    Loopify cannot yet lower two self-calls in sequence at [itree E unit]
    (tests/wip/itree_two_self_calls). *)
Crane NoLoopify quicksort_ST.

Crane Extraction "st_quicksort" STQuicksort.

Crane Benchmark
  STQuicksort.test_quicksort_fun,
  STQuicksort.test_quicksort_ST
On C++ With "".
