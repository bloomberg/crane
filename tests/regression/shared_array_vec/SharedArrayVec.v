(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A sequence mapped to [crane::shared_array], as ParseALot maps its DFA
    tables: built from a list, nested, indexed, matched on, extended at the
    front, and copied into a list, whose copies share the arrays. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedArrayVec.

Inductive vec (X : Type) : Type :=
| vnil : vec X
| vcons : X -> vec X -> vec X.

Arguments vnil {X}.
Arguments vcons {X} _ _.

Fixpoint vec_of_list {X} (l : list X) : vec X :=
  match l with [] => vnil | h :: t => vcons h (vec_of_list t) end.

Fixpoint vec_nth {X} (v : vec X) (n : nat) (d : X) : X :=
  match v, n with
  | vnil, _ => d
  | vcons h _, O => h
  | vcons _ t, S m => vec_nth t m d
  end.

Fixpoint vec_sum (v : vec nat) : nat :=
  match v with vnil => 0 | vcons h t => h + vec_sum t end.

Definition table : vec (vec nat) :=
  vec_of_list (map vec_of_list [[1; 2; 3]; [4; 5]; []; [6]]).

Definition copies : list (vec (vec nat)) := [table; table; vcons (vec_of_list [7]) table].

Definition result : nat :=
  vec_nth (vec_nth table 1 vnil) 1 0                          (* 5 *)
  + vec_nth (vec_nth table 2 vnil) 0 100                      (* 100 *)
  + vec_sum (vec_nth table 0 vnil)                            (* 6 *)
  + fold_left (fun acc t => acc + vec_sum (vec_nth t 0 vnil)) copies 0. (* 6+6+7 *)

End SharedArrayVec.

(* Lists as [crane::list], as ParseALot's ConsList.v has them: an array is
   built from one by walking it. *)
Crane Extract Inductive list =>
  "crane::list<%t0>"
  [ "crane::list<%t0>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  From "conslist.h".
Crane Extract Inductive SharedArrayVec.vec =>
  "crane::shared_array<%t0>"
  [ "crane::shared_array<%t0>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  From "shared_array.h".
Crane Extract Inlined Constant SharedArrayVec.vec_of_list =>
  "crane::shared_array<%t0>::of_range(%a0)" From "shared_array.h".
Crane Extraction "shared_array_vec" SharedArrayVec.
