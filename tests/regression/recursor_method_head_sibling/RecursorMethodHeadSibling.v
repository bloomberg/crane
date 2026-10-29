(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** A type-indexed family's recursor, made a method, next to an unrelated
    inductive.

    With [chain] declared beside [expr], [expr_rect] becomes a method of
    [expr] (alone, it stays a function), and the method's head drops the
    index variable [T2].  The check that the body names no variable the
    head dropped reported that it names [T2], though the printed C++ names
    it nowhere: the method's own self-call carries every type argument,
    and is printed on its receiver without the ones the head dropped.  The
    check now reads a method callee's type arguments as they are printed. *)
Module RecursorMethodHeadSibling.

Inductive expr : Type -> Type :=
| lit : nat -> expr nat
| bl : bool -> expr bool
| succE : expr nat -> expr nat.

Inductive chain : Type :=
| base : nat -> chain
| next : chain -> chain.

Definition sample : expr nat := succE (lit 1).

Definition sample_chain : chain := next (base 1).

End RecursorMethodHeadSibling.

Crane Extraction "recursor_method_head_sibling" RecursorMethodHeadSibling.
