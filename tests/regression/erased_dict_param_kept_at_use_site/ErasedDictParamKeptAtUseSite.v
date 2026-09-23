(* An instance's erased dictionary parameter is dropped from the declaration
   and kept at the use site.

     template <IPtr _tcI0> struct ParamsV { ... };          // one parameter
     Iface::template use<ParamsV<IPZ, std::any>>(n);        // two arguments

   [IPtrTheory] has only [Prop] fields, so the dictionary erases.  Erasing it
   from the template head is right, and so is writing something in the
   argument position if the head had kept it; the two sides disagree about
   whether it did.

   The discriminator is the {e arity gap}, not the error count: the
   declaration must take one parameter and the use site must pass two.  A run
   where both became one, or both two, reports zero errors without this being
   fixed -- it is the test no longer reaching the defect.  The tell that the
   use site knew the argument was erased and wrote a placeholder anyway, as
   opposed to not knowing about the parameter at all, is that the argument is
   literally [std::any]:

     ParamsV<IPZ, std::any>     the defect
     ParamsV<IPZ, IPZTheory>    the erasure did not happen
     ParamsV<IPZ>               both sides agreed

   Giving [IPtrTheory] a [Set] field moves both sides together, to
   [template <IPtr _tcI0, IPtrTheory _tcI1>] and [ParamsV<IPZ, IPZTheory>], so
   the two are not independently computed from the instance's arity: one of
   them consults erasure and the other does not.

   Which side is wrong is not settled by that.  The use site could erase too,
   or the declaration could keep the slot as a phantom -- which is what
   reified ITree mode already does, with [TTtypename_default Tvoid], for the
   same reason that removing a parameter breaks every positional argument
   list.

   Vellvm: [vellvm_bench.cpp:10330] and [:10335] against the declaration at
   [vellvm_bench.h:12950], from [@ParamsV IPZ IPZTheory] at
   [rocq/Semantics/TopLevel.v:320] and [rocq/Semantics/Run.v:126]. *)

From Crane Require Import Mapping.Std.

Class IPtr := { iptr : Set ; zero : iptr }.

Class IPtrTheory {IP : IPtr} := { zero_eq : zero = zero }.

Class Params := { IPTR : IPtr ; width : nat }.

Definition use `{Pa : Params} (n : nat) : nat := n + width.

#[global] Instance IPZ : IPtr := { iptr := nat ; zero := 0 }.
#[global] Instance IPZTheory : @IPtrTheory IPZ := { zero_eq := eq_refl }.

#[global] Instance ParamsV {IP : IPtr} {IPT : @IPtrTheory IP} : Params :=
  { IPTR := IP ; width := 64 }.

Module ErasedDictParamKeptAtUseSite.

  Definition go (n : nat) : nat := @use (@ParamsV IPZ IPZTheory) n.

End ErasedDictParamKeptAtUseSite.

Crane Extraction "erased_dict_param_kept_at_use_site" ErasedDictParamKeptAtUseSite.
