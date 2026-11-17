(** A carrier written as a constructor's field, inside a module.

    [Mine]'s field is written through a synthesised alias for [itree noE],
    naming [Inner]'s own [noE], and [Theirs]'s through one for
    [itree outerE], naming the enclosing module's.  A constructor's fields
    are written in a scope of the inductive's own, which is no module: the
    aliases used to be declared at namespace scope, in front of the outer
    struct, where the names they spell are undeclared.  Each is declared in
    [Inner]'s struct, the module whose member writes it. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module AliasHomeConstructorField.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant outerE : Type -> Type := .

  Module Inner.
    Variant noE : Type -> Type := .

    Inductive box : Type :=
    | Mine : stateT nat (itree noE) nat -> box
    | Theirs : stateT nat (itree outerE) nat -> box.

    Definition tag (b : box) : nat := match b with Mine _ => 0 | Theirs _ => 1 end.
  End Inner.

  Definition five : nat := 5.
End AliasHomeConstructorField.

Crane Extraction "alias_home_constructor_field" AliasHomeConstructorField.
