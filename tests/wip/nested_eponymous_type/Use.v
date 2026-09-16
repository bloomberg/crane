From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import OrderedType.
From CraneTestsWIP Require nested_eponymous_type.Compare.
From CraneTestsWIP Require nested_eponymous_type.Other.

Module NestedEponymousType.
  Definition use {X : Type} {lt eq : X -> X -> Prop} {x y : X}
                 (c : Compare lt eq x y) : bool :=
    andb (Compare.cmp_lt c) (andb (Compare.is_lt 1) (Other.is_lt 1)).
End NestedEponymousType.

Crane Extraction "nested_eponymous_type" NestedEponymousType.
