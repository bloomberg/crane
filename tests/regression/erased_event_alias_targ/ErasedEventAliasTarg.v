(* A type abbreviation over a section variable the backend erases.

   [semantic_function := list nat -> itree E nat] mentions the event family
   [E], and the reified backend writes no [E] in C++ at all.  The parameter is
   therefore phantom: not a [template <typename> class] -- declaring it one
   would demand a template of every use site for a position that holds
   nothing -- but a plain parameter defaulted to [void], and a use spells the
   erased family's head where it would otherwise spell an instantiation of it.

   A constant over such a family is a variable template, so that its type has
   somewhere to name the parameter its uses supply.

   In Vellvm this was most of the 48 "use of undeclared identifier" errors:
   [semantic_function] and [intrinsic_definitions] in
   rocq/Semantics/IntrinsicsDefinitions.v, both inside [Section Intrinsics]
   with [Context {E} `{FailureE -< E}]. *)From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Section S.
  Context {E} `{FailE -< E}.

  Definition semantic_function := list nat -> itree E nat.

  Definition k : semantic_function := fun args => Ret (length args).
End S.

Module ErasedEventAliasTarg.
  Definition use (l : list nat) : itree FailE nat := k l.
End ErasedEventAliasTarg.

Crane Extraction "erased_event_alias_targ" ErasedEventAliasTarg.
