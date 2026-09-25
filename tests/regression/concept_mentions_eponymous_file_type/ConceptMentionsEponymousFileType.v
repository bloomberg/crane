(** A hoisted concept spells an inductive that is printed inside a file
    module's struct, which C++ gives no way to forward-declare.

    [list] is declared in [Datatypes], but once a function from the Stdlib
    file [List] is extracted -- [nth_error] here -- that file becomes
    [struct List], and [list] is printed inside it as its eponymous type,
    [List::list<A>].  The concept prerequisites travel with the concept
    ([tests/regression/concept_mentions_alias_and_module_type]), and they
    reach [DList] and [DString] here, but the struct that [List::list] names
    is not one of them: it stays where the file prints it, below the
    concept.

    Expected: [struct List], and what its own body needs ([Nat]), precedes
    the aliases and the concept.
    Actual:   error: use of undeclared identifier 'List'
              at [template <typename a> using DList = std::function<List::list<a>(List::list<a>)>;]

    Without [nth_error] there is no [struct List], [list] prints as the
    forward-declared [List<A>], and everything compiles.  Seen in Vellvm at
    install #15 (1109cc29d), where the same wrapper blocks the whole header
    from parsing. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Definition DList (A : Type) : Type := list A -> list A.
Definition DString : Type := DList bool.

Class DShow (A : Type) : Type :=
  { dshow : A -> DString
  ; dlist : A -> list nat }.

#[global] Instance dshowNat : DShow nat :=
  {| dshow := fun _ l => true :: l
   ; dlist := fun n => n :: nil |}.

Module ConceptMentionsEponymousFileType.
  Definition run : list bool := dshow 3 nil.
  Definition run2 : list nat := dlist 4.
  Definition run3 : option nat := nth_error (dlist 5) 0.
End ConceptMentionsEponymousFileType.
Crane Extraction "concept_mentions_eponymous_file_type" ConceptMentionsEponymousFileType.
