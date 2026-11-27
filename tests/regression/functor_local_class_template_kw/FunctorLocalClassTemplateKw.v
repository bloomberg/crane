From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** A class declared inside a functor is reached, after instantiation, through
    a [template] disambiguator that does not belong there: the generated code
    says [FN::template use(...)] for a plain member, and clang answers "'use'
    following the 'template' keyword does not refer to a template". *)

Module Type S.
  Parameter t : Type.
  Parameter z : t.
End S.

Module F (X : S).
  Class Cl := { get : X.t }.
  Global Instance inst : Cl := { get := X.z }.
  Definition use (c : Cl) : X.t := @get c.
End F.

Module N <: S.
  Definition t := nat.
  Definition z := 0.
End N.

Module FN := F N.

Module FunctorLocalClassTemplateKw.
  Definition run : nat := FN.use FN.inst.
End FunctorLocalClassTemplateKw.

Crane Extraction "functor_local_class_template_kw" FunctorLocalClassTemplateKw.
