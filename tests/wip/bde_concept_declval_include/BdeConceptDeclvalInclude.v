(** Found by Ephyra round 23 (BDE flavour; there inside a [Crane Bake]
    unit). A module type with a function parameter [op : t -> t -> t]
    becomes a concept whose requires-clause calls
    [M::op(bsl::declval<typename M::t>(), ...)], but the header does not
    include <bsl_utility.h>, the header that declares [bsl::declval] (it
    includes bsl_concepts, bsl_functional, bsl_memory, bsl_string, ...).
    Expected: compiles, [result = 8].
    Actual: "no template named 'declval' in namespace 'bsl'; did you mean
    'std::declval'?". Also on main. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Import Extraction.

Module BdeConceptDeclvalInclude.

Module Type SIG.
  Parameter t : Type.
  Parameter op : t -> t -> t.
End SIG.

Module N <: SIG.
  Definition t := nat.
  Definition op := Nat.add.
End N.

Module F (E : SIG).
  Definition twice (x : E.t) : E.t := E.op x x.
End F.

Module FN := F N.

Definition result : nat := FN.twice 4.

End BdeConceptDeclvalInclude.

Crane Extraction "bde_concept_declval_include" BdeConceptDeclvalInclude.
