(* Rocq bug #16288: extraction of primitive projections within a functor
   were incorrectly referencing themselves *)

Require Crane.Extraction.
From Crane Require Mapping.Std.

Module RocqBug16288.

Module Type Nop. End Nop.
Module Empty. End Empty.
Module M (N : Nop).
  Local Set Primitive Projections.
  Record M_t_NonEmpty elt := { M_m :> list elt }.
  Record M_t_NonEmpty' X Y := { a : X ; b : Y }.
End M.
Module M' := M Empty.

End RocqBug16288.

Crane Extraction "rocq_bug_16288" RocqBug16288.
