(** Crane bug: a carrier holder for [stateT _ (itree AllE)], where the family
    alias [AllE] comes from another file, is declared at the top of the
    header, ahead of [AllE] itself:
      template <typename _P0> struct _crane_carrier_tch {
        template <typename _CraneTcArg>
        using c = Itree<AllE<typename _P0::ptr, std::any>, _CraneTcArg>; };
      ...
      template <typename ptr, typename x> using AllE = Sum1<MemE<ptr>, FailE, x>;
    giving [use of undeclared identifier 'AllE'].  A single-file layout keeps
    [AllE] in the module struct and places the holder there correctly; only
    a family from another file is at namespace scope, reached by the
    wrapper struct of the file module that uses it ([HoStack]).

    Reduced from Vellvm: [_crane_carrier_tch1] over [MCFGEbot] (from the file
    LLVMEvents.v) is declared at h:1380, [MCFGEbot] at h:15664 -- Vellvm's one
    remaining parse error on bac0be39f. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
From CraneTestsRegression Require Import carrier_holder_file_order.HoEvents carrier_holder_file_order.HoStack.

#[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

Module CarrierHolderFileOrder.
  Definition first (_ : unit) : itree AllE (nat * nat) := get_st 1 2.
End CarrierHolderFileOrder.

Crane Extraction "carrier_holder_file_order" CarrierHolderFileOrder.
