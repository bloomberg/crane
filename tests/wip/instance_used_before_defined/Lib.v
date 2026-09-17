(** Crane bug: an instance referenced from a global's initializer is emitted
    after that global, and a forward declaration is not enough.

    [Ops.Arith_nat] is a global whose initializer contains a lambda calling
    [ret] at [EOU_monad]:

       15 | struct EOU_monad;                       // forward declaration
      175 |   static inline const Arith<Nat> Arith_nat =
      177 |       return Monad0::template ret<EOU_monad, Nat>(...);
      186 | struct EOU_monad { ... };               // definition

    [Monad0::ret] names [typename _tcI0::template m<T2>], which needs the
    complete type, so the forward declaration does not carry it.  The
    reference is only reachable through a lambda inside a global initializer,
    which is what the ordering pass appears not to walk.

    Expected: [struct EOU_monad] precedes [Arith_nat].
    Actual:   error: no matching function for call to 'ret'
              note: candidate template ignored: substitution failure
                    [with _tcI0 = EOU_monad, T2 = Nat]: incomplete type
                    'EOU_monad' named in nested name specifier
              error: no viable conversion from '(lambda at ...)' to
                     'std::function<EOU<Nat> (Nat, Nat)>'

    [Arith] is a Record rather than a Class on purpose: that is what makes the
    instance a struct literal with std::function fields, as Vellvm's
    [VMemInt_Z] is.  With a Class the instance becomes a struct of static
    methods and is ordered correctly.

    Seen in Vellvm on [VellvmIntegers.VMemInt_Z] against [EOU_monad], and on
    [RelDec_zeq] the same way: 16 "no matching function for call to 'ret'"
    plus 8 "no viable conversion", against instances all emitted together in
    one block at 19797-19850, after their users. *)

From Crane Require Extraction.
From ExtLib Require Import Structures.Monads.

Variant EOU {X : Type} : Type :=
  | raise_error (s : nat) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU : clear implicits.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
     bind _ _ c k :=
       match c with
       | raise_error s => raise_error s
       | raise_ret x => k x
       end
  |}.
