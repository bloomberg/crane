(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: nested module types used by declared functors inside module types. *)

Module TodoNestedModuleTypeFunctor.

Module Type OUTER.
  Module Type INNER.
    Parameter t : Type.
    Parameter zero : t.
  End INNER.

  Declare Module X : INNER.
  Declare Module Make (I : INNER) : INNER.
End OUTER.

Module Use (Y : OUTER).
  Module Lifted := Y.Make Y.X.

  Definition test_value : Lifted.t :=
    Lifted.zero.
End Use.

End TodoNestedModuleTypeFunctor.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Extraction "todo_nested_module_type_functor" TodoNestedModuleTypeFunctor.
