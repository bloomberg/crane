(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local [cofix] that takes no parameters -- [cofix o := Cons 1
    o] inside an expression -- does not compile.  The local-cofix path
    assumes at least one parameter: it emits
    [auto o_impl = [=](auto &) { return stream::cons(1, o); };
     auto o = [=]() { o_impl(o_impl); }; return o;]
    -- the body names [o] rather than its self argument ("use of undeclared
    identifier 'o'"), nothing suspends the corecursive occurrence, the outer
    lambda returns nothing, and the lambda itself is returned where a
    [stream] is expected.  A local cofix with parameters, and a top-level
    parameterless [CoFixpoint], both work. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LocalCofixWithoutParameters.

CoInductive stream := Cons : nat -> stream -> stream.

Definition hd (s : stream) : nat := match s with Cons x _ => x end.

Fixpoint take (k : nat) (s : stream) : list nat :=
  match k with 0 => [] | S k' => match s with Cons x t => x :: take k' t end end.

Definition zeros_or (b : bool) : stream :=
  if b then (cofix z : stream := Cons 0 z) else (cofix o : stream := Cons 1 o).

Definition ones_then (l : list nat) : stream := fold_right Cons (cofix o := Cons 1 o) l.

Definition result : nat :=
  hd (zeros_or true) + hd (zeros_or false) + fold_left Nat.add (take 4 (ones_then [5; 6])) 0.

End LocalCofixWithoutParameters.

Crane Extraction "local_cofix_without_parameters" LocalCofixWithoutParameters.
