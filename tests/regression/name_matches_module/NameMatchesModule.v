From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** A module becomes a C++ struct, so a definition or an inductive named after
    its enclosing module becomes a member with the same name as its class,
    which C++ forbids.  Both spellings are here: [Inner] inside module [Inner],
    and [NameMatchesModule] inside module [NameMatchesModule]. *)

Module NameMatchesModule.

  Module Inner.
    Inductive Inner := I : nat -> Inner.
    Definition get (x : Inner) : nat := match x with I n => n end.
  End Inner.

  Definition NameMatchesModule : nat := 4.

  Definition run : nat := NameMatchesModule + Inner.get (Inner.I 6).

End NameMatchesModule.

Crane Extraction "name_matches_module" NameMatchesModule.
