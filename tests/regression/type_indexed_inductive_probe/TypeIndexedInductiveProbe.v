From Crane Require Extraction.

Module TypeIndexedInductiveProbe.

(** Regression test for type-indexed inductives with erased type parameters.

    Inductive [wrap] is indexed by a [Set]; the type parameter [A] is erased
    in C++, so the field [d_a] is typed [std::any].  When matching [w : wrap
    bool] at the concrete index [bool], the branch body [b] must be recovered
    via [std::any_cast<Bool0>].  Previously Crane emitted a bare [return d_a]
    instead, causing a compile error:
      error: no viable conversion from 'std::any' to 'const Bool0' *)

Inductive wrap : Set -> Type :=
| Wrap : forall A : Set, A -> wrap A.

Definition w : wrap bool := Wrap bool true.

Definition sample : bool :=
  match w with
  | Wrap _ b => b
  end.

End TypeIndexedInductiveProbe.

Crane Extraction "type_indexed_inductive_probe" TypeIndexedInductiveProbe.
