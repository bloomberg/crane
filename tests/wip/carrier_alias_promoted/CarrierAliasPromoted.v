(** Crane bug: the carrier alias for [itree E] with [E] mentioning a
    promoted class instance's type field is emitted at file scope with the
    instance variable free.

    Observed (0b9b536f0):
      template <typename _CraneTcArg>
      using _crane_carrier_tc_b2b3658f40108d9d =
          Itree<memE<typename _tcI0::PTR...>, _CraneTcArg>;   // _tcI0 free at file scope
      ...
      template <typename _tcI0> ...
      static stateT<Nat, _crane_carrier_tc_b2b3658f40108d9d, Nat> get_st(Nat n)
    Diagnostics:
      error: use of undeclared identifier '_tcI0'
      error: use of undeclared identifier '_crane_carrier_tc_b2b3658f40108d9d'
      error: no matching function for call to 'get_st'
    Expected: the holder that 0b9b536f0 uses for a plain family in a result
    type ([_crane_carrier_tch<...>::template c]), instantiated at the
    function's own [_tcI0]-dependent family.

    Reduced from Vellvm on 0b9b536f0: the artifact's .cpp opens with
      template <typename _CraneTcArg>
      using _crane_carrier_tc_c043b3081d64c112 = Itree<
          MCFGEbot<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr, std::any>,
          _CraneTcArg>;
    and the handlers ([InterpretationStack.on_mem] etc.) use it in
    [stateT<State<...>, _crane_carrier_tc_c043b3081d64c112, T1>]
    (41 parse errors). *)

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
