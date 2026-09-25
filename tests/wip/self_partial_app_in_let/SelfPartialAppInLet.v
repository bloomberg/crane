(** A fixpoint that binds a partial application of itself.

    Stdlib's [Pos.peano_rect] is

      let f2 := peano_rect (fun p => P p~0) (f _ a) (fun p x => f _ (f _ x)) in
      match p with ... f2 q ... end

    -- two of its three value arguments, bound as a function of the third.
    The recursive call is emitted as a call with two arguments,

      std::function<T1(Positive)> f2 = peano_rect<T1>(f(Positive::xh(), a), ...);

    and a function of three parameters has no two-argument overload:

      error: no matching function for call to 'peano_rect'

    Seen in Vellvm at install #18, where [BinNat.peano_rect] (through
    [N.recursion] and [ListUtil.repeatN]) instantiates it; one of the last 15
    errors. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PArith.

Module SelfPartialAppInLet.
  Definition run : nat := Pos.peano_rect (fun _ => nat) 0 (fun _ n => S n) 5%positive.
End SelfPartialAppInLet.
Crane Extraction "self_partial_app_in_let" SelfPartialAppInLet.
