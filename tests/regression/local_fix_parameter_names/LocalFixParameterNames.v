(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local fixpoint's generated [_impl] lambda declares its
    parameters under different names than its body uses.  In [walk2 (f :
    nat)], the mutual local fix [F]/[G] is printed with [F] as [f0], so
    [G]'s own parameter, also [f0], is renamed [f1] in its body -- but the
    [_impl] lambda's parameter list is built apart from that renaming, and
    leaves the parameter unnamed: "use of undeclared identifier 'f1'".
    Equations produces this shape for [with] clauses and [Derive
    NoConfusion]-backed definitions, so those fail the same way. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LocalFixParameterNames.

Definition walk2 (f : nat) : list nat -> nat :=
  fix F (l : list nat) {struct l} : nat := match l with [] => f | _ :: t => G t end
  with G (f0 : list nat) {struct f0} : nat := match f0 with [] => f + 1 | _ :: t => F t end
  for F.

Definition result : nat := walk2 5 [1; 2; 3].

End LocalFixParameterNames.

Crane Extraction "local_fix_parameter_names" LocalFixParameterNames.
