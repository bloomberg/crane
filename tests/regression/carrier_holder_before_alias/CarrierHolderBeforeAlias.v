(** The carrier holder for [itree AllE] with [AllE := memE +' failE] over
    a promoted class field.  In Vellvm the holder was printed before the
    alias it names ([vellvm_bench.h:1383: use of undeclared identifier
    'MCFGEbot'], e888c04f0).

    That ordering defect no longer reproduces here: [get_st] compiles.

    Fixed (2026-11-26): the same defect as carrier_alias_promoted.
    [is_three] matched [observe r] at the struct's [using ptr =
    crane::obj] ([ItreeF<Sum1<memE<crane::obj>, FailE, crane::obj>, ...>])
    while [r] is an [Itree<Sum1<memE<Nat>, ...>>]; [std::get] failed its
    [static_assert].  Here [r]'s recorded shape is [itree] applied to
    [@AllE natParams], an alias, not an instance; a class argument that is
    no instance now supplies what its own arguments do. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module CarrierHolderBeforeAlias.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  (* Vellvm's [Params]: a class whose field is a type. *)
  Class Params : Type := { ptr : Type ; zero : ptr }.

  Section WithParams.
    Context {Pa : Params}.
    Variant memE : Type -> Type := Load : ptr -> memE nat.
    Variant failE : Type -> Type := Fail : failE unit.
    Definition AllE := memE +' failE.

    (* Vellvm's handlers: [stateT S (itree E)] with E mentioning the class's
       type field, in a function's result type. *)
    Definition get_st (n : nat) : stateT nat (itree AllE) nat :=
      fun s => Ret (s + n, s).
  End WithParams.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

  Definition r : itree AllE (nat * nat) := get_st 1 2.
  Definition is_three : bool :=
    match observe r with RetF (a, _) => Nat.eqb a 3 | _ => false end.
End CarrierHolderBeforeAlias.

Crane Extraction "carrier_holder_before_alias" CarrierHolderBeforeAlias.
