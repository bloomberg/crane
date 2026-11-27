From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** A module alias is transparent to Rocq but not to the factory-method namer:
    reached through the alias [A], the constructor [c] of [Lib.t] is called as
    [A::t::c0(...)], while the type declares the factory as [c].  Using [Lib]
    directly works; only the aliased path gets the [0] suffix. *)

Module Lib.
  Inductive t := c : nat -> t.
  Definition get (x : t) : nat := match x with c n => n end.
End Lib.

Module A := Lib.

Module ModuleAliasFactoryName.
  Definition run : nat := A.get (A.c 3).
End ModuleAliasFactoryName.

Crane Extraction "module_alias_factory_name" ModuleAliasFactoryName.
