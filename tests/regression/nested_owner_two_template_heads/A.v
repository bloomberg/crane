From Crane Require Import Mapping.Std.

(** A polymorphic inductive at namespace scope.  [Bag.v] declares a file-level
    module of the same name, so the wrapper this is written under holds that
    module's declarations beside it and is not written as one struct with it:
    the datatype keeps its own name underneath, and is spelled [Bag::bag] from
    outside. *)
Inductive bag (A : Set) : Set := | Empty : bag A | Add : A -> bag A -> bag A.

Arguments Empty {A}.
Arguments Add {A} _ _.
