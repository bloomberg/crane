(** The carrier for [itree E] with [E] mentioning a promoted class
    instance's type field, in a function's result type ([stateT nat
    (itree memE) nat]).  Reduced from Vellvm on 0b9b536f0 (the handlers of
    [InterpretationStack.on_mem] etc.).

    The defect it was filed for (a file-scope alias with [_tcI0] free) is
    gone: [get_st] is now written against the holder
    [crane_carrier_tch<_tcI0>::template c].

    Fixed (2026-11-26): [is_three]'s match over [observe r] spelled the
    scrutinee's constructors at the struct's [using ptr = crane::obj]
    ([ItreeF<memE<crane::obj>, ...>]) while [r] is an
    [Itree<memE<Nat>, ...>], resolved through [natParams] in [r]'s own body;
    [std::get] failed its [static_assert].  A reader resolves a referenced
    global's promoted variables off the class shape recorded from its Rocq
    type, and [r : itree (@memE natParams) _] recorded [itree]'s, whose
    arguments name no class; the search through the type now keeps such a
    shape only where no applied type names a class, so [r] records
    [@memE natParams]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module CarrierAliasPromoted.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  (* Vellvm's [Params]: a class whose field is a type. *)
  Class Params : Type := { ptr : Type ; zero : ptr }.

  Section WithParams.
    Context {Pa : Params}.
    Variant memE : Type -> Type := Load : ptr -> memE nat.

    (* Vellvm's handlers: [stateT S (itree E)] with E mentioning the class's
       type field, in a function's result type. *)
    Definition get_st (n : nat) : stateT nat (itree memE) nat :=
      fun s => Ret (s + n, s).
  End WithParams.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

  Definition r : itree memE (nat * nat) := get_st 1 2.
  Definition is_three : bool :=
    match observe r with RetF (a, _) => Nat.eqb a 3 | _ => false end.
End CarrierAliasPromoted.

Crane Extraction "carrier_alias_promoted" CarrierAliasPromoted.
