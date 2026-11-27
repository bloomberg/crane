(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Union-find (disjoint sets over [0 .. n - 1]), twice.

    Both versions keep a forest in which every element points to a parent and
    roots point to themselves; each node also carries a rank. [find] follows
    parent links to the root and then points every visited node straight at
    it (path compression); [union] links the root of smaller rank under the
    root of larger rank, bumping the rank on a tie (union by rank).

    - [find_ST], [union_ST], [same_ST] work in place on an ST array of
      [(parent, rank)] nodes, extracted to a [std::vector]; each is a C++
      function of its own taking the array. A read or write is
      O(1), so a sequence of [m] operations on [n] elements costs
      O(m α(n)), α the inverse Ackermann function, plus O(n) for [make_ST].
    - [find_fun], [union_fun], [same_fun] are the same algorithm on a
      persistent AVL map ([FMapAVL]) from elements to nodes, where a missing
      element is a root of rank 0, so [empty_uf] is the initial partition.
      A lookup or update costs O(log n), so operations cost O(α(n) log n)
      amortized when the structure is used linearly, and O(log² n) each in
      the worst case (union by rank alone bounds paths by log n).

    [find] recurses on a fuel argument, which is always the element count [n].
    Fuel never runs out: parent links are acyclic and stay within [0 .. n - 1],
    so a path to a root visits fewer than [n] nodes ([find_fun_root] in
    [UnionFindProofs]). The fuel is decremented once per step, so it does not
    change the complexity.

    [UnionFindProofs] shows that [union_find_ST] computes [union_find_fun]. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Wf_nat
  Lia
  List
  FSets.FMapAVL
  Structures.OrderedTypeEx
.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.STMonad
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** A node of the forest: its parent and its rank. *)
Definition node : Type := nat * nat.

(** A batch of operations: [Union x y] merges the sets of [x] and [y],
    [Same x y] asks whether they are in the same set. *)
Inductive op : Type :=
| Union (x y : nat)
| Same (x y : nat).

Section Imperative.

  Context {R : STRefs}.

  Notation V := (fun _ : nat => node).
  Notation E0 := (STEvent R V +' exceptE Err).

  (** Makes each element from [i] up to [n - 1] a root of rank 0.  It
      recurses on the accessibility of [n - i], which is erased, and is a
      tail call: it extracts to a loop writing the cells in place. *)
  #[refine] Fixpoint init_ST (a : STArray node) (n i : nat) (acc : Acc lt (n - i))
    {struct acc} : itree E0 unit :=
    match Sumbool.sumbool_of_bool (Nat.ltb i n) with
    | left Hlt =>
      writeArray a i (i, 0);;
      init_ST a n (S i) (@Acc_inv _ _ _ acc (n - S i) _)
    | right _ => Ret tt
    end.
  Proof. apply Nat.ltb_lt in Hlt. lia. Defined.

  (** [Acc_intro_generator] puts [2^10] layers of [Acc_intro] in front of
      [lt_wf], so that [make_ST] also computes in Rocq. *)
  Definition make_ST (n : nat) : itree E0 (STArray node) :=
    a <- newArray n (0, 0);;
    init_ST a n 0 (Acc_intro_generator 10 lt_wf _);;
    Ret a.

  (** The operations take the array as a section variable rather than as an
      argument of the recursion: see [UnionFind] below. *)
  Section Operations.

    Context (n : nat) (a : STArray node).

    Fixpoint find_ST (fuel : nat) (x : nat) : itree E0 nat :=
      match fuel with
      | O => Ret x
      | S fuel' =>
          '(p, k) <- readArray a x;;
          if p =? x then Ret x
          else
            r <- find_ST fuel' p;;
            writeArray a x (r, k);;
            Ret r
      end.

    Definition union_ST (x y : nat) : itree E0 unit :=
      rx <- find_ST n x;;
      ry <- find_ST n y;;
      if rx =? ry then Ret tt
      else
        '(_, kx) <- readArray a rx;;
        '(_, ky) <- readArray a ry;;
        if kx <? ky then writeArray a rx (ry, kx)
        else if ky <? kx then writeArray a ry (rx, ky)
        else (writeArray a ry (rx, ky);; writeArray a rx (rx, S kx)).

    Definition same_ST (x y : nat) : itree E0 bool :=
      rx <- find_ST n x;;
      ry <- find_ST n y;;
      Ret (rx =? ry).

    Fixpoint run_ST (ops : list op) : itree E0 (list bool) :=
      match ops with
      | [] => Ret []
      | Union x y :: ops' => union_ST x y;; run_ST ops'
      | Same x y :: ops' =>
          b <- same_ST x y;;
          bs <- run_ST ops';;
          Ret (b :: bs)
      end.

  End Operations.

  (** Answers to the [Same] queries of [ops], on [n] elements. *)
  Definition union_find_ST (n : nat) (ops : list op) : itree E0 (list bool) :=
    a <- make_ST n;;
    run_ST n a ops.

End Imperative.

Module NatMap := FMapAVL.Make Nat_as_OT.

Definition uf : Type := NatMap.t node.

Definition empty_uf : uf := NatMap.empty node.

Definition get (s : uf) (x : nat) : node :=
  match NatMap.find x s with
  | Some nd => nd
  | None => (x, 0)
  end.

Fixpoint find_fun (fuel : nat) (s : uf) (x : nat) : nat * uf :=
  match fuel with
  | O => (x, s)
  | S fuel' =>
      let '(p, k) := get s x in
      if p =? x then (x, s)
      else
        let '(r, s') := find_fun fuel' s p in
        (r, NatMap.add x (r, k) s')
  end.

Definition union_fun (n : nat) (s : uf) (x y : nat) : uf :=
  let '(rx, s) := find_fun n s x in
  let '(ry, s) := find_fun n s y in
  if rx =? ry then s
  else
    let '(_, kx) := get s rx in
    let '(_, ky) := get s ry in
    if kx <? ky then NatMap.add rx (ry, kx) s
    else if ky <? kx then NatMap.add ry (rx, ky) s
    else NatMap.add rx (rx, S kx) (NatMap.add ry (rx, ky) s).

Definition same_fun (n : nat) (s : uf) (x y : nat) : bool * uf :=
  let '(rx, s) := find_fun n s x in
  let '(ry, s) := find_fun n s y in
  (rx =? ry, s).

Fixpoint run_fun (n : nat) (s : uf) (ops : list op) : list bool :=
  match ops with
  | [] => []
  | Union x y :: ops' => run_fun n (union_fun n s x y) ops'
  | Same x y :: ops' =>
      let '(b, s) := same_fun n s x y in
      b :: run_fun n s ops'
  end.

Definition union_find_fun (n : nat) (ops : list op) : list bool :=
  run_fun n empty_uf ops.

Module UnionFind.

  (** The ST side is extracted one function per operation: [find_ST],
      [union_ST], [same_ST] and [run_ST] take the array, a
      [std::shared_ptr<std::vector<node>>], by const reference, and write
      its elements through it. *)
  Definition union_find_ST := @union_find_ST cpp_refs.

  Definition union_find_fun := Eval unfold union_find_fun in union_find_fun.

End UnionFind.

Set Crane Loopify.

Crane Extraction "union_find" UnionFind.
