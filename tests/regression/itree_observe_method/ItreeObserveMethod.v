(** Crane bug: ITree's [observe] (a Definition over the [_observe]
    projection) is methodified onto [Itree] with its event parameter still
    treated as a template name.

    Observed, in the generated [struct Itree]:
      template <typename T1> ItreeF<E, R, Itree<E, R>> observe() const {
        const auto &[_observe] =
            std::get<typename Itree<T1<std::any>, R>::Go>(this->v());
    [T1<std::any>] applies a plain [typename] as a template.  Diagnostics:
      error: expected '>'
      error: type name requires a specifier or qualifier
      error: declaration of 'R' shadows template parameter
      error: structured binding declaration must be the only declaration in its group

    Control: matching on the projection [_observe] directly instead of
    [observe] compiles (and [void1] as the event is not the cause either).

    Follows the coind_family_param fix (a8a63b2d7), which fixed a
    user-defined projection; this is the library's [observe] Definition.
    Reduced from Vellvm's vanilla-ITree extraction (src/crane/Extract.v with
    Mapping.Std only): every [ITree.bind]/[ITree.iter] goes through
    [ITree.subst], which matches on [observe u]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module ItreeObserveMethod.
  Variant noE : Type -> Type := .
  Definition t : itree noE nat := Ret 3.
  Definition is_three : bool :=
    match observe t with RetF r => Nat.eqb r 3 | _ => false end.
End ItreeObserveMethod.

Crane Extraction "itree_observe_method" ItreeObserveMethod.
