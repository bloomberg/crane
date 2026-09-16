(** Crane bug: the rename that resolves a file eponymous with a type it
    declares does not fire when the type is a *definition* (a C++ alias)
    rather than an inductive.

    [DList.v] declares [DList], a [Definition] returning a function type, and
    [DList_append] over it.  Crane emits both the alias and the file's struct
    under the same name:

      template <typename a> using DList = std::function<...>;
      struct DList { ... };

    With an inductive in the same position the module gives way and is renamed
    [DList0], which is what d77449c8 made it do.

    Expected: the module is renamed, as for an inductive.
    Actual:   error: redefinition of 'DList' as different kind of symbol
              note: previous definition is here

    Seen in Vellvm on [Utils/DList.v]. *)

From Crane Require Extraction.
From Stdlib Require Import List.

Definition DList (a : Type) := list a -> list a.

Definition DList_append {a : Type} (d1 d2 : DList a) : DList a :=
  fun xs => d1 (d2 xs).

Definition DList_empty {a : Type} : DList a := fun xs => xs.
