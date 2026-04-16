From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashLetMatch.

(** Tests for variable name clashes between let-bindings and match bindings. *)

Inductive either : Type :=
| Left : nat -> either
| Right : nat -> either.

Inductive triple : Type :=
| MkTriple : nat -> nat -> nat -> triple.

(** Variable name 'a' used in both let and match binding. *)
Definition let_shadows_match (e : either) : nat :=
  let a := 100 in
  match e with
  | Left a => a    (* should shadow the let binding *)
  | Right b => b + a
  end.

(** Match binding used in a nested let that shadows. *)
Definition match_then_let (e : either) : nat :=
  match e with
  | Left x =>
    let x := x + 1 in  (* shadows match binding *)
    x
  | Right y => y
  end.

(** Two either values matched in sequence, same field names. *)
Definition two_eithers (e1 e2 : either) : nat :=
  let v1 := match e1 with Left x => x | Right x => x * 2 end in
  let v2 := match e2 with Left x => x | Right x => x * 3 end in
  v1 + v2.

(** Match on a triple, then match on an either, same-ish names *)
Definition triple_then_either (t : triple) (e : either) : nat :=
  match t with
  | MkTriple a b c =>
    let from_either := match e with Left x => x | Right x => x end in
    a + b + c + from_either
  end.

(** Deeply nested let-match-let-match chain *)
Definition deep_let_match (e1 e2 e3 : either) : nat :=
  let a := match e1 with Left x => x | Right x => x end in
  let b := match e2 with
           | Left y =>
             let z := match e3 with Left w => w | Right w => w end in
             y + z
           | Right y => y
           end in
  a + b.

(** Match where the same variable name is used in multiple branches *)
Definition same_name_branches (e : either) (t : triple) : nat :=
  match e with
  | Left val =>
    match t with
    | MkTriple x y z => val + x + y + z
    end
  | Right val =>
    match t with
    | MkTriple x y z => val * x * y * z
    end
  end.

End NameClashLetMatch.

Crane Extraction "name_clash_let_match" NameClashLetMatch.
