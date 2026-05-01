From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module MutualValueDeepDestruct.

(** Same mutual-recursive ownership shape as the copy test, but this test does
    not copy the value.  It isolates destruction: dropping a deep alternating
    [a]/[b] value currently recurses through the default [unique_ptr] destructor
    chain.  The generated classes do not get an iterative mutual destructor, so
    leaving scope after building a deep value overflows the C++ stack. *)

Inductive a : Type :=
| AEnd : a
| ANode : bool -> b -> a
with b : Type :=
| BNode : a -> b.

Definition keep_a (x : a) : a := x.

End MutualValueDeepDestruct.

Crane Extraction "mutual_value_deep_destruct" MutualValueDeepDestruct.
