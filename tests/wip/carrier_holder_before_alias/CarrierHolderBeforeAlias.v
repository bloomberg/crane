(** Crane bug: the carrier holder for [itree AllE] (e888c04f0's
    [_crane_carrier_tch<_tcI0>]) is emitted before the family alias it names.

    Observed (e888c04f0):
      template <typename _P0> struct _crane_carrier_tch {   // h:340
        template <typename _CraneTcArg> using c = Itree<AllE<...>, _CraneTcArg>;
      ...
      template <typename ptr, typename x> using AllE = Sum1<memE<ptr>, FailE, x>;   // h:372, later
    Diagnostic:
      error: use of undeclared identifier 'AllE'
      error: no matching function for call to 'get_st'
    Here [AllE] is also nested in the module struct (the placement issue of
    partial_app_carrier / carrier_alias_promoted).  In Vellvm the alias is
    at file scope but simply later: the holder is at h:1380 and
    [using MCFGEbot = Sum1<...>] at h:15664, giving
      vellvm_bench.h:1383: error: use of undeclared identifier 'MCFGEbot'
    (Vellvm's only parse error on e888c04f0).  The holder needs to follow
    everything its body names. *)

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
