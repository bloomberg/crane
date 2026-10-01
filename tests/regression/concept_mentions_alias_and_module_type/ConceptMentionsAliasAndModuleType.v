(** Crane bug: a concept hoisted to the top of the file names types that are
    declared further down, and two kinds of name cannot be rescued by the
    forward declarations that precede it.

    Hoisting a file-scope concept to the top is correct for most of what a
    concept mentions: the body of a [requires] expression is unevaluated, so
    a plain mention is satisfied by a forward declaration, and those are
    already emitted first.  Two kinds are not.

    - A [using] alias has no forward declaration in C++ at all.  [Name] is
      one, and the concept spells it in the result of [show].
    - A name used {e qualified} -- [Coll::bag] -- needs the definition and
      not a declaration, because a member is being looked up in it.  A module
      is emitted as a struct and is not forward-declared at all, so this one
      has neither.

    Expected: the concept follows every name it cannot merely have declared.
    Actual:   error: use of undeclared identifier 'Name'
              error: use of undeclared identifier 'Coll'
              plus the four wrecked diagnostics behind those two.

    Seen in Vellvm as three referents across 21 concepts -- the aliases
    [DString] and [memM], and [List] used as [List::list<...>] -- accounting
    for 10 direct diagnostics and 7 wrecked [expected] diagnostics behind
    them. *)

From Crane Require Import Extraction.

(** Named qualified by the concept, so a forward declaration will not do. *)
Module Coll.
  Inductive bag (A : Type) : Type :=
    | Nil : bag A
    | Cons : A -> bag A -> bag A.
  Arguments Nil {A}.
  Arguments Cons {A}.
End Coll.

(** An alias, which is the kind of declaration C++ cannot forward-declare. *)
Definition Name : Type := Coll.bag nat.

Class Show (A : Type) : Type :=
  { show : A -> Name
  ; tag : A -> Coll.bag bool }.

#[global] Instance showNat : Show nat :=
  {| show := fun n => Coll.Cons n Coll.Nil
   ; tag := fun _ => Coll.Cons true Coll.Nil |}.

Module ConceptMentionsAliasAndModuleType.
  Definition run : Name := show 3.
End ConceptMentionsAliasAndModuleType.
Crane Extraction "concept_mentions_alias_and_module_type" ConceptMentionsAliasAndModuleType.
