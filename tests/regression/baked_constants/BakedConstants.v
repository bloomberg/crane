(* SPDX-License-Identifier: BSD-3-Clause *)
(** [Crane Bake]: closed constants computed when the command runs and
    extracted as data, under [Set Crane SharedVariant]: a DAG whose shared
    subterms stay shared, a mapped random-access sequence of sequences (static
    blocks), a mapped string and option, and the constants that cannot be
    baked. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List String Ascii.
Import ListNotations.

Set Crane SharedVariant.

Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Module BakedConstants.

(** A random-access sequence, mapped to [crane::shared_array] as the
    parse-a-lot lexer's tables are. *)
Inductive vec (A : Type) : Type := vnil | vcons (a : A) (v : vec A).
Arguments vnil {A}.
Arguments vcons {A} a v.

Fixpoint vec_of_list {A} (l : list A) : vec A :=
  match l with [] => vnil | x :: xs => vcons x (vec_of_list xs) end.

Fixpoint vec_nth {A} (v : vec A) (n : nat) (d : A) : A :=
  match v, n with
  | vnil, _ => d
  | vcons x _, 0 => x
  | vcons _ v', S m => vec_nth v' m d
  end.

Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).

(** [build n] has [2^n - 1] nodes, but only [n] distinct ones: each node's
    two children are one value. *)
Fixpoint build (n : nat) : tree :=
  match n with 0 => Leaf | S m => let t := build m in Node t n t end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => 1 + size l + size r end.

Fixpoint sum_tree (t : tree) : nat :=
  match t with Leaf => 0 | Node l x r => sum_tree l + x + sum_tree r end.

(** Baked: a DAG of 16 nodes standing for 65535. *)
Definition big : tree := build 16.

(** Baked: a table of rows, two of them the same row. *)
Definition row (k : nat) : vec nat := vec_of_list (map (fun i => i * k) (seq 0 10)).
Definition table : vec (vec nat) * vec bool :=
  let r := row 3 in (vec_of_list [row 1; r; r; vnil], vec_of_list [true; false; true]).

(** Baked: a list of labelled records holding strings and options. *)
Record entry : Type := { name : string; weight : option nat; label : tree }.
Definition entries : list entry :=
  [ {| name := "first"; weight := Some 7; label := build 2 |};
    {| name := ""; weight := None; label := Leaf |} ].

Definition big_size (u : unit) : nat := size big.
Definition big_sum (u : unit) : nat := sum_tree big.
Definition cell (i j : nat) : nat := vec_nth (vec_nth (fst table) i vnil) j 0.
Definition accept (i : nat) : bool := vec_nth (snd table) i false.
Definition names (u : unit) : string :=
  fold_right (fun e acc => append (name e) acc) EmptyString entries.
Definition weights (u : unit) : nat :=
  fold_right (fun e acc => match weight e with Some w => w + acc | None => acc end) 0 entries.

(** What cannot be baked. *)
Definition twice (n : nat) : nat := n + n.
Definition a_type : Type := nat.
Record with_fn : Type := { fn : nat -> nat }.
Definition boxed_fn : with_fn := {| fn := twice |}.
CoInductive stream : Type := Cons (hd : nat) (tl : stream).
CoFixpoint ones : stream := Cons 1 ones.
Definition a_proof : 0 = 0 := eq_refl.

End BakedConstants.

Crane Extract Inductive BakedConstants.vec =>
  "crane::shared_array<%t0>"
  [ "crane::shared_array<%t0>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  From "shared_array.h".

Crane Extract Inlined Constant BakedConstants.vec_nth =>
  "(static_cast<std::size_t>(%a1) < (%a0).size() ? (%a0)[static_cast<std::size_t>(%a1)] : %a2)".

Crane Bake BakedConstants.big BakedConstants.table BakedConstants.entries.

Fail Crane Bake BakedConstants.twice.
Fail Crane Bake BakedConstants.a_type.
Fail Crane Bake BakedConstants.boxed_fn.
Fail Crane Bake BakedConstants.ones.
Fail Crane Bake BakedConstants.a_proof.
Fail Crane Bake BakedConstants.tree.

Crane Extraction "baked_constants" BakedConstants.
