(** Crane bug: a pattern lambda over [FusedS := state * ...] (with [state] a
    section-local instance's type field) rebuilds the tuple with the
    [state] component boxed into [std::any].

    Observed (after binder_type_names_section_field):
      return [=](FusedS<typename _tcI0::ptr> pat) mutable {     // binder spelled right now
        const auto &[m, p] = pat; ...
          std::make_pair(std::make_pair(std::any(m), std::make_pair(ls, g_)), r) ...
    [m] is a [St<...>]; wrapping it in [std::any] makes the result
    [pair<pair<std::any, ...>, ...>], which does not convert to the declared
    [pair<FusedS<...>, T>].  Diagnostics:
      error: no viable conversion from 'pair<__unwrap_ref_decay_t<std::pair<std::any, ...>>, [...]>'
             to 'pair<std::pair<St<Nat>, ...>, [...]>'
      error: no viable conversion from 'std::any' to 'List<Nat>'

    Reduced from Vellvm, [Semantics/InterpretationStack.v:65-71]
    ([on_ls] / [on_genv := fun '(m, (ls, g)) => '(g', r) <- f g;; ret ((m, (ls, g')), r)]):
    [std::make_pair(std::make_pair(std::any(m), std::make_pair(ls, g_)), r)],
    giving the [ret] errors in on_genv/on_ls and the [make_pair] errors in
    update_globals_ref / update_locals_ref. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From ITree Require Import ITree Events.State.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

Module PatternBinderStateBoxed.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Class MemState {Pa : Params} : Type := { state : Type ; initial_state : state }.
  Class MemPrims {Pa : Params} : Type := { mm_state :: @MemState Pa ; bump : nat -> nat }.

  Section Impl.
    Context {Pa : Params}.
    Record St : Type := mkSt { mem : list ptr }.
    #[global] Instance MemStateV : @MemState Pa := { state := St ; initial_state := mkSt [] }.
    #[global] Instance MemPrimsV : @MemPrims Pa := { mm_state := MemStateV ; bump := S }.
  End Impl.

  Variant noE : Type -> Type := .

  Section Stack.
    Context {Pa : Params}.
    Existing Instance MemPrimsV.
    Definition FusedS : Type := (state * (list nat * nat))%type.
    (* Vellvm's InterpretationStack.on_genv: destructure FusedS with a
       pattern lambda, run the component handler, rebuild FusedS. *)
    Definition on_genv {T} (f : Monads.stateT nat (itree noE) T) : Monads.stateT FusedS (itree noE) T :=
      fun '(m, (ls, g)) => '(g', r) <- f g ;; Ret ((m, (ls, g')), r).
    Definition incr : Monads.stateT nat (itree noE) nat := fun g => Ret (S g, g).
    Definition go (_ : unit) : itree noE (FusedS * nat) := on_genv incr (initial_state, ([], 4)).
  End Stack.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition t := go tt.
End PatternBinderStateBoxed.

Crane Extraction "pattern_binder_state_boxed" PatternBinderStateBoxed.
