From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashReturnThis.

(** Test: match-as-expression where one branch returns the scrutinee itself.
    When methodified, this becomes `return this` which is a raw pointer,
    but the IIFE lambda expects shared_ptr. *)

Inductive shape : Type :=
| Circle : nat -> shape
| Square : nat -> nat -> shape.

(** Inner match returns shape in all branches, one branch returns the
    argument itself. The function takes shape as input, so it gets
    methodified. In the Blue branch, `s` becomes `this`. *)
Definition maybe_transform (flag : bool) (s : shape) : shape :=
  match flag with
  | true =>
    match s with
    | Circle r => Square r r
    | Square w h => Circle (w + h)
    end
  | false => s  (* this becomes `return this` when methodified *)
  end.

(** Match on shape where one branch returns the same shape unchanged. *)
Definition identity_or_double (s : shape) : shape :=
  match s with
  | Circle r => Circle (r * 2)
  | Square w h => Square w h  (* could become identity, returns same ctor *)
  end.

(** Two shapes, return one of them based on a match on the other. *)
Definition pick_shape (s1 s2 : shape) : shape :=
  match s1 with
  | Circle _ => s2
  | Square _ _ => s1  (* returns `this` when methodified on s1 *)
  end.

(** Nested: match on result of a function that may return this *)
Definition nested_this (s : shape) : nat :=
  match identity_or_double s with
  | Circle r => r
  | Square w h => w + h
  end.

End NameClashReturnThis.

Crane Extraction "name_clash_return_this" NameClashReturnThis.
