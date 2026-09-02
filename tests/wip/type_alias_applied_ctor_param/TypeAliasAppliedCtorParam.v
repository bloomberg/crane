From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module TypeAliasAppliedCtorParam.

(** A type-level definition that applies its own type-constructor argument
    becomes a C++ alias template whose first parameter is a plain [typename]
    but is then used as a template:

      template <typename f, typename a> using ap = f<a>;
      ...
      ap<F<std::any>, Nat> a0;

    error: expected ';' after alias declaration
    error: expected '>'

    [f] needs to be [template <typename> class f], and the use site must pass
    [F], not [F<std::any>]. *)

Definition ap (F : Type -> Type) (A : Type) : Type := F A.

Inductive holder (F : Type -> Type) := hold : ap F nat -> holder F.
Arguments hold {F} _.

Definition mk : holder option := hold (Some 1).

Definition get (h : holder option) : option nat := match h with hold x => x end.

End TypeAliasAppliedCtorParam.

Crane Extraction "type_alias_applied_ctor_param" TypeAliasAppliedCtorParam.mk TypeAliasAppliedCtorParam.get.
