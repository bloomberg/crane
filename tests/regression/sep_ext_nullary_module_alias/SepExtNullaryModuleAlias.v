(** Regression: nullary field accessed through a local module alias in a
    functor body must be called with () in C++.
    Pattern: functor Worker takes (C : Config), creates a local alias
    Module MyV := C.V, then accesses MyV.empty. In C++ this becomes
    using MyV = typename C::V; and MyV::empty should be MyV::empty().
    Mirrors the ConcreteTable pattern where
    using reFS = typename R::Defs::reFS; and reFS::empty is missing (),
    and the Impl0 pattern where Memo::emptyMemo is missing (). *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.

Module Type HasVal.
  Parameter t : Type.
  Parameter empty : t.
End HasVal.

Module Type Config.
  Declare Module V : HasVal.
  Parameter default_val : nat.
End Config.

Module Worker (C : Config).

  Module MyV := C.V.

  Definition get_empty : MyV.t := MyV.empty.

  Definition get_default : nat := C.default_val.

End Worker.

Crane Separate Extraction Worker.
