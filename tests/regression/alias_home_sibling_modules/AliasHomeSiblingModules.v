(** One carrier spelling, homed in two sibling modules.

    [A.a_id] and [B.b_id] are each written through a synthesised alias for
    [itree e], each module declaring its own [e].  An alias's name is a
    digest of its body as written in its home, and both bodies are written
    [Itree<e, _>], so both are one name; the file declared that name once,
    in [A], and [B]'s use named nothing in [B].  Each module's struct now
    declares it, where its own [e] is meant. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module AliasHomeSiblingModules.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Module A.
    Variant e : Type -> Type := .
    Definition a_id (m : stateT nat (itree e) nat) : stateT nat (itree e) nat := m.
  End A.

  Module B.
    Variant e : Type -> Type := .
    Definition b_id (m : stateT nat (itree e) nat) : stateT nat (itree e) nat := m.
  End B.

  Definition five : nat := 5.
End AliasHomeSiblingModules.

Crane Extraction "alias_home_sibling_modules" AliasHomeSiblingModules.
