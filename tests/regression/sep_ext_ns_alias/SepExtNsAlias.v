(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: a plain (non-functor) module alias must emit
   `namespace R = Foo;` in C++, not the invalid `using R = Foo;`.
   Non-functor modules become C++ namespaces; namespace aliases
   require the `namespace` keyword, not `using`. *)

Module Foo.
  Definition x : nat := 0.
End Foo.

Module FooAlias := Foo.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction FooAlias.
