(** The carrier for [itree E] with [E] mentioning a promoted class
    instance's type field, in a function's result type ([stateT nat
    (itree memE) nat]).  Reduced from Vellvm on 0b9b536f0 (the handlers of
    [InterpretationStack.on_mem] etc.).

    The defect it was filed for (a file-scope alias with [_tcI0] free) is
    gone: [get_st] is now written against the holder
    [crane_carrier_tch<_tcI0>::template c].

    Open (diagnosed 2026-11-24): [is_three]'s match over [observe r].  [r]
    is declared [Itree<memE<typename natParams::ptr>, pair<Nat, Nat>>]: its
    body names [natParams] ([get_st<natParams>]), so
    [Decl_state.with_body_resolutions] resolves the promoted [ptr].
    [is_three]'s body names only [r], so nothing resolves [ptr] there and
    the match spells the scrutinee's constructors at the struct's
    [using ptr = crane::obj]: [std::get<ItreeF<memE<crane::obj>, ...>::RetF>]
    on a variant of [ItreeF<memE<Nat>, ...>] fails [static_assert] in
    [std::get].  [type_resolutions_of_referenced_globals] reads a
    referenced global's resolutions only off a recorded class shape of its
    type ([@dval natIPtr]), and [r]'s type ([itree (@memE natParams) _])
    records none: the instance sits under the head.  The connection is in
    the Rocq type at [extract_constant] ([Base.Table.instance_class_shapes]),
    which records only the head's own class arguments; recording the
    instances an argument's family is applied to, or resolving a reader's
    types through the resolutions its referenced globals were declared
    under, would close it. *)

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
