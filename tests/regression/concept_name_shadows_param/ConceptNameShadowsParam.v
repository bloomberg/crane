(** A module type whose name is a single letter.  Crane emits the concept with
    a template parameter of the same name, which shadows the concept itself:

    {v
      template <typename M> concept M = requires { ... };
      redefinition of 'M' as different kind of symbol
      unknown type name 'M'
    v} *)

Require Crane.Extraction.

Module ConceptNameShadowsParam.

Module Type M. Parameter f : nat -> nat. End M.
Module Use (X : M). Definition g (n : nat) := X.f n. End Use.
Module Id <: M. Definition f (n : nat) := n. End Id.
Module U := Use Id.

Definition test := U.g 1.

End ConceptNameShadowsParam.

Crane Extraction "concept_name_shadows_param" ConceptNameShadowsParam.
