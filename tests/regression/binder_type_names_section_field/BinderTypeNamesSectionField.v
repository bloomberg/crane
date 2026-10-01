(** Crane bug: a lambda binder whose type is a definition over a
    section-local instance's [Type] field spells the field bare -- the
    file-scope [std::any] -- where the declaration's own type writes the
    definition by name:
      template <Params _tcI0, ...>
      static stateT<FusedS<typename _tcI0::ptr>, ..., T1> fused(...) {
        return [=](std::pair<state, Nat> s) mutable { ... };
    The binder's annotation is the definition unfolded, and [state] in it
    names no instance in [fused]'s scope; the slot, the declared return
    type unfolded, spells it [FusedS<...>].

    Reduced from Vellvm, [Semantics/InterpretationStack.v] [fused_trigger]
    ([fun _ e s => r <- trigger e;; ret (s, r)] at [stateT FusedS (itree
    MCFGEbot)]), where [ret (s, r)] then builds [pair<std::any, ...>]
    against the expected [pair<FusedS, T>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From ITree Require Import ITree.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

Module BinderTypeNamesSectionField.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Class MemState {Pa : Params} : Type := { state : Type ; init : state ; sz : state -> nat }.

  Section Impl.
    Context {Pa : Params}.
    Record St : Type := mkSt { mem : list ptr }.
    #[local] Instance MemStateV : @MemState Pa :=
      { state := St ; init := mkSt [] ; sz := fun s => length (mem s) }.
    Definition FusedS : Type := (state * nat)%type.
    Variant cntE : Type -> Type := Cnt : cntE nat.
    Definition fused : cntE ~> Monads.stateT FusedS (itree cntE) :=
      fun _ e s => r <- trigger e ;; Ret (s, r).
    Definition size_of (s : FusedS) : nat := sz (fst s) + snd s.
    Definition start (n : nat) : FusedS := (init, n).
    Definition after_cnt (n : nat) : itree cntE (FusedS * nat) := fused _ Cnt (start n).
  End Impl.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition is_five : bool := Nat.eqb (size_of (start 5)) 5.
End BinderTypeNamesSectionField.

Crane Extraction "binder_type_names_section_field" BinderTypeNamesSectionField.
