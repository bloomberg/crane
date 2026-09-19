(* An inductive with a lower-case Rocq name normally extracts to a capitalised
   C++ struct, and everything agrees.  When the inductive is folded into a
   file-struct wrapper (because a nested module's name collides with a type),
   the *declaration* keeps the lower-case name while every *reference* is
   capitalised, so nothing resolves.

   Expected: [struct Dval { ... }] to match the [Dval] used throughout.
   Actual:
       struct dval {                                 // declared lower-case
         Dval clone() const { return {n}; }          // referenced capitalised
         static Dval dv_nat(Nat n) { ... }
       };
       static Dval mk(Nat n);
       static Dval go(const Nat &x0_);
     error: unknown type name 'Dval'; did you mean 'dval'?   (x4)

   In Vellvm this is the "unknown type name 'X'; did you mean 'X'?" pair plus
   part of the 3 bare "unknown type name" errors.  Vellvm's own [dvalue] and
   [dvalue_base] capitalise correctly wherever they are *not* folded into a
   wrapper struct, which is what makes the wrapper path the trigger. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import NArith.
From CraneTestsWIP Require Import Helper.

Module FoldedInductiveNotCapitalized.
  Definition go (n : nat) : dval := mk n.
  Definition m : N := Helper.N.two.
End FoldedInductiveNotCapitalized.

Crane Extraction "folded_inductive_not_capitalized" FoldedInductiveNotCapitalized.
