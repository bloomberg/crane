(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A definition inside a module that names a definition of the same name
    outside it, at file scope.  In C++ the member shadows the outer
    definition throughout its struct, so the reference has to be spelled so
    that it reaches the outer one; written bare, a function alias recursed
    forever and a constant alias initialised itself from itself. *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Definition dbl (n : nat) : nat := n + n.
Definition seven : nat := 7.

Module ModuleAliasShadowsGlobal.
  (** Two levels down, naming the file-scope definitions, which the members
      of this module and of the enclosing one both hide. *)
  Module R.
    Definition dbl := dbl.
    Definition seven := seven.
  End R.

  Module Type HasX.
    Parameter x : nat.
  End HasX.

  (** A functor's struct, naming the file-scope definitions its members
      hide. *)
  Module F (X : HasX).
    Definition dbl := dbl.
    Definition seven := seven.
    Definition r : nat := dbl (X.x + seven).
  End F.

  Module Three.
    Definition x : nat := 3.
  End Three.

  Module F3 := F Three.

  Definition dbl := dbl.
  Definition seven := seven.
  (** A definition of another file, which a collision wrapper holds. *)
  Definition even := Nat.even.
  (** Uses the two aliases, which are now the members. *)
  Definition t : nat := dbl seven.

  (** Names the members of the enclosing module, which its own hide. *)
  Module Q.
    Definition dbl (n : nat) : nat := dbl (dbl n).
    Definition seven : nat := seven + 1.
    Definition u : nat := dbl seven.
  End Q.
End ModuleAliasShadowsGlobal.

Crane Extraction "module_alias_shadows_global" ModuleAliasShadowsGlobal.
