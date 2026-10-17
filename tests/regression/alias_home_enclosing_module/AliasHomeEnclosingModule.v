(** A carrier naming a type of another module inside the same struct.

    [mixed], in [Inner], is written through a synthesised alias for
    [itree outerE], whose body names the enclosing module's [outerE];
    [deep_outer], in [Inner.Deeper], one for [itree Inner.noE]; and [after],
    back in the outer module, one for [itree Inner.noE] again.  None names
    the module it is written in, and each used to be declared at namespace
    scope, in front of the outer struct, where the qualified names it spells
    are undeclared.  Each is declared inside the struct whose member writes
    it, where they are. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module AliasHomeEnclosingModule.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant outerE : Type -> Type := .

  Module Inner.
    Variant noE : Type -> Type := .

    Definition mixed (m : stateT nat (itree outerE) nat) : stateT nat (itree outerE) nat := m.

    Module Deeper.
      Definition deep_outer (m : stateT nat (itree noE) nat) : stateT nat (itree noE) nat := m.
    End Deeper.
  End Inner.

  Definition after (m : stateT bool (itree Inner.noE) nat) : stateT bool (itree Inner.noE) nat := m.

  Definition five : nat := 5.
End AliasHomeEnclosingModule.

Crane Extraction "alias_home_enclosing_module" AliasHomeEnclosingModule.
