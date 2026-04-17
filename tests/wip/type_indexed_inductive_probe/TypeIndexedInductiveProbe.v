From Crane Require Extraction.

Module TypeIndexedInductiveProbe.

(** WIP: Type-indexed inductive stores constructor payload as std::any but
    the generated match returns it directly as the concrete C++ type without
    an std::any_cast, producing a compile error.

    Inductive [wrap] is indexed by a [Set]; the type parameter [A] is erased
    in C++, so the field [d_a] is typed [std::any].  When matching [w : wrap
    bool] at the concrete index [bool], the branch body [b] should be
    recovered via [std::any_cast<Bool0>], but Crane emits a bare [return d_a]
    instead, which fails with:
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
