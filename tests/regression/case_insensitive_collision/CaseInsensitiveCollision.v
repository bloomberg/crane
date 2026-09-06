From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** Crane capitalises an inductive's name to form its C++ type, so the
    inductive [bar] and the definition [Bar] both want to be [Bar].  The
    generated code then has to say [enum Bar] to name the type at all, and the
    two are indistinguishable at the use site. *)

Module CaseInsensitiveCollision.

  Definition foo : nat := 1.
  Definition Foo : nat := 2.

  Inductive bar := B1 | B2.

  Definition Bar (b : bar) : nat := match b with B1 => 3 | B2 => 4 end.

  Definition run : nat := foo + Foo + Bar B2.

End CaseInsensitiveCollision.

Crane Extraction "case_insensitive_collision" CaseInsensitiveCollision.
