(** Crane bug (runtime): a Monad instance at an alias of an applied type
    ([EOUP Z := EOU (MaybePoison Z)]) declares its carrier as the outer
    type constructor alone.

    Observed (9506ee474):
      struct EOUP_Monad {
        template <typename _A0> using m = EOU<_A0>;        // should be EOU<MaybePoison<_A0>>
        template <typename _A0> static EOU<MaybePoison<_A0>> ret(_A0 a) { ... }
    so [Monad0::ret<EOUP_Monad, nat>] returns [m<nat> = EOU<Nat>] built by
    converting an [EOU<MaybePoison<Nat>>], and at run time the converting
    constructor hits the inactive field:
      libc++abi: terminating due to uncaught exception of type
      std::logic_error: unreachable: inactive constructor field at this instantiation

    Reduced from Vellvm, [Semantics/MemoryBytes.v:76-90] ([MaybePoison],
    [EOUP], [EOUP_Monad], [dvalue_base_extract_byte]): the alloca-churn
    benchmark aborts with exactly this, thrown from
    [EOU<Z>::EOU<MaybePoison<Z>>] under [Monad0::ret<EOUP_Monad, Z>] in
    [MemoryBytes::dvalue_base_extract_byte]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

Module MonadAliasOfApplied.
  (* Vellvm's Semantics/EOU.v *)
  Variant EOU {X : Type} : Type :=
  | raise_error (n : nat) : EOU
  | raise_ret (x : X) : EOU.
  Arguments EOU : clear implicits.
  #[global] Instance EOU_monad : Monad EOU :=
    {| ret := @raise_ret ;
       bind _ _ c k := match c with raise_error s => raise_error s | raise_ret x => k x end |}.

  (* MemoryBytes.v:76-88: a monad on an alias of an applied type,
     EOUP Z := EOU (MaybePoison Z), whose ret wraps NoPois. *)
  Variant MaybePoison (A : Type) : Type := Pois | NoPois (a : A).
  Arguments Pois {A}. Arguments NoPois {A}.
  Definition EOUP Z := EOU (MaybePoison Z).
  #[local] Instance EOUP_Monad : Monad EOUP :=
    {| ret _ a := ret (NoPois a) ;
       bind _ _ c k := bind (m := EOU) c (fun pov => match pov with
                                                    | Pois => ret Pois
                                                    | NoPois a => k a end) |}.

  (* MemoryBytes.v:90 dvalue_base_extract_byte *)
  Definition extract (b : bool) (n : nat) : EOUP nat :=
    if b then ret (S n) else @ret EOU _ _ Pois.

  Definition is_three : bool :=
    match extract true 2 with raise_ret (NoPois k) => Nat.eqb k 3 | _ => false end.
End MonadAliasOfApplied.

Crane Extraction "monad_alias_of_applied" MonadAliasOfApplied.
