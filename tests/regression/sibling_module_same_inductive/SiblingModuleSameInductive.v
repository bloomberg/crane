From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module SiblingModuleSameInductive.

(** Two sibling submodules each declare an inductive named [t].  Both are
    nested structs, so neither shadows a global-scope [t]; the out-of-line
    definitions must stay plainly qualified:

      Nat SiblingModuleSameInductive::A::get(
          const SiblingModuleSameInductive::A::t &x) *)

Module A.
  Inductive t := mk : nat -> t.
  Definition get (x : t) : nat := match x with mk n => n end.
End A.

Module B.
  Inductive t := mk : bool -> t.
  Definition get (x : t) : bool := match x with mk b => b end.
End B.

Definition run (n : nat) : nat := A.get (A.mk n).
Definition run2 (b : bool) : bool := B.get (B.mk b).

End SiblingModuleSameInductive.

Crane Extraction "sibling_module_same_inductive" SiblingModuleSameInductive.
