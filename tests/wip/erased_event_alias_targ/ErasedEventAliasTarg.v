(* A section-level type abbreviation that mentions the event family becomes a
   C++ alias.  In the reified backend the event is erased, so the alias is
   emitted with *no* template head at all -- but every use site still passes
   an argument for the erased event, naming an undeclared [T1].

   Expected: [const semantic_function k = ...]  (or the alias keeping a
             parameter and the use site passing [void], as 79cf29afc does for
             phantom function template arguments).
   Actual:
       using semantic_function = std::function<std::shared_ptr<ITree<Nat>>(List<Nat>)>;
       const semantic_function<T1> k = ...
     error: use of undeclared identifier 'T1'

   In Vellvm this is most of the 48 "use of undeclared identifier" errors.
   [semantic_function] is rocq/Semantics/IntrinsicsDefinitions.v:380, inside
   [Section Intrinsics] with [Context {E} `{FailureE -< E} ...].  There the
   alias does keep a head (vellvm_bench.h:11306,
   [template <template <typename> class e> using semantic_function = ...]),
   but the eight users still write [semantic_function<T1>] -- vellvm_bench.h
   :11447, :11478, :15466, :15576, :15609, :15641.  Same for
   [intrinsic_definitions<T1>] (IntrinsicsDefinitions.v:383). *)
From Crane Require Import Extraction.
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
