(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   WIP test: Crane emits unqualified type name for an inductive defined
   inside a Module, when that type is referenced from outside the Module
   and separate extraction is used.

   In parse-a-lot, `Module Export Labels` defines `Inductive Label'` and
   `Definition Label := Label'`. A functor application produces a type
   alias `Rule := Label * regex`. Definitions outside the module (e.g.
   `ru_float : Rule`) reference `Label` which resolves to `Labels.Label'`.
   Under separate extraction, Crane generates `Label_` in the type
   annotation instead of `Labels::Label_`, causing a C++ compilation error.
*)
From Stdlib Require Import List.
Import ListNotations.

Require Crane.Extraction.

(* Module type requiring a Tag type *)
Module Type HasTag.
  Parameter Tag : Type.
  Parameter defTag : Tag.
End HasTag.

(* A functor that uses the Tag type to define a Rule alias *)
Module Type RuleSig (T : HasTag).
  Definition Rule := (T.Tag * nat)%type.
End RuleSig.

Module RuleMod (T : HasTag) <: RuleSig T.
  Definition Rule := (T.Tag * nat)%type.
End RuleMod.

(* A module implementing HasTag with an inductive — mimics Labels in parse-a-lot *)
Module Export Tags <: HasTag.
  Inductive Tag' : Type :=
  | Foo
  | Bar
  | Baz.

  Definition Tag : Type := Tag'.
  Definition defTag : Tag := Foo.
End Tags.

(* Functor application — mimics Module Export LXR := LexerFn Alphabet Labels *)
Module Export RM := RuleMod Tags.

(* Definitions outside the module referencing Rule (= Tag * nat) *)
(* These mimic ru_float, ru_int etc. in parse-a-lot *)
Definition my_rule : Rule := (Bar, 42).
Definition my_rule2 : Rule := (Baz, 7).

Definition get_tag (r : Rule) : Tag := fst r.
Definition test_tag : Tag := get_tag my_rule.

Set Crane Loopify.
Crane Separate Extraction my_rule my_rule2 get_tag test_tag.
