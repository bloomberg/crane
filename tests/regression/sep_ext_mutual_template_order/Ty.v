From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Inductive tree (A : Type) := Node : A -> forest A -> tree A
with forest (A : Type) := Nil : forest A | Cons : tree A -> forest A -> forest A.
Arguments Node {A}. Arguments Nil {A}. Arguments Cons {A}.
