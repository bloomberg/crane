From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** A type defined in a sibling module is spelled relative to the extraction
    target in the generated [.cpp], not relative to the enclosing namespace:
    the out-of-line definition of [f] says [SiblingModuleTypeQualified::Lib::t]
    even though [Lib] is a sibling of the target, giving "no member named
    'Lib'".  The header, which spells the same type from inside the namespace,
    is fine — only the [.cpp] disagrees.  Nesting the defining module deepens
    the wrong prefix but does not change it. *)

Module Lib.
  Inductive t := c : nat -> t.
  Module Inner.
    Inductive u := d : nat -> u.
  End Inner.
End Lib.

Module SiblingModuleTypeQualified.
  Definition f (x : Lib.t) : nat := match x with Lib.c n => n end.
  Definition g (y : Lib.Inner.u) : nat := match y with Lib.Inner.d n => n end.
  Definition run : nat := f (Lib.c 1) + g (Lib.Inner.d 2).
End SiblingModuleTypeQualified.

Crane Extraction "sibling_module_type_qualified" SiblingModuleTypeQualified.
