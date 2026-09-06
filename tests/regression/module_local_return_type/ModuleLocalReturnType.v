From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** An out-of-line definition spells its return type *before* the qualified
    function name, so the enclosing struct's scope is not yet open there.  A
    function returning a type declared in a nested module is emitted as
    [M::t ModuleLocalReturnType::make(...)], and [M] is undeclared at that
    point.  Parameter types, which come after the qualified name, are fine. *)

Module ModuleLocalReturnType.

  Module M.
    Inductive t := C : nat -> t.
  End M.

  Definition make (n : nat) : M.t := M.C n.

  Definition run : nat := match make 4 with M.C n => n end.

End ModuleLocalReturnType.

Crane Extraction "module_local_return_type" ModuleLocalReturnType.
