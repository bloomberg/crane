From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Structures.Functor Data.Monads.OptionMonad.
From CraneTestsWIP Require fwd_decl_before_concept.Lib.

Module FwdDeclBeforeConcept.
  Definition use (o : option nat) : option bool :=
    @fmap option (@Lib.Functor_Monad option Monad_option) nat bool
          (fun n => Nat.eqb n 0) o.
End FwdDeclBeforeConcept.

Crane Extraction "fwd_decl_before_concept" FwdDeclBeforeConcept.
