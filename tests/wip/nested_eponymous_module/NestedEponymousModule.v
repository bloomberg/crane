(** A module nested inside a module of the same name.  Both become structs, and
    C++ forbids a member with the same name as its enclosing class:

    {v
      member 'Inner' has the same name as its class
      no member named 'v' in 'NestedEponymousModule::Inner'
    v} *)

Require Crane.Extraction.

Module NestedEponymousModule.

Module Inner.
  Module Inner.
    Definition v : nat := 3.
  End Inner.
  Definition w : nat := Inner.v.
End Inner.

Definition test : nat := Inner.w.

End NestedEponymousModule.

Crane Extraction "nested_eponymous_module" NestedEponymousModule.
