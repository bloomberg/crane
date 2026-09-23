(* A definition whose body is a conditional returning functions, with the final
   argument not written.  Crane eta-expands it -- correctly, the C++ signature
   needs the argument -- but introduces the new parameter outside the
   conditional rather than inside its branches:

     return (PeanoNat::even(n)
                 ? [=](Nat _x0) mutable -> Nat { return f_even(n, _x0); }
                 : [=](Nat _x0) mutable -> Nat { return f_odd(n, _x0); })(
         std::move(x0_));

     error: incompatible operand types ('(lambda at ...)' and '(lambda at ...)')

   Both lambdas have the same signature and no common type: each closure type
   is unique and neither converts to the other, so the conditional expression
   is ill-formed.  It is applied to [x0_] immediately, which makes the output
   gratuitous as well as invalid -- two closures are built so that one of them
   can be called on the spot.

   The defect is in the composition, not in either part.  Writing the
   eta-expansion in Rocq instead ([Definition pick (n x : nat) := if ... then
   f_even n x else f_odd n x]) gives a plain if/else with a call in each branch
   and compiles, so pushing the parameter into the branches is both well-formed
   and what the source-level version already produces.

   Reduced from Vellvm's use of Flocq's SpecFloat.new_location, which is
   point-free in exactly this way.

   Third of three defects where a closure lands where C++ needs a nameable
   function type, and the only one with no erasure in it: see
   erased_arg_callable_spelled_std_function and
   loop_transform_reassigns_closure_typed_var, which are both consequences of a
   callable rebuilt because an erased proof argument forced it. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.

Definition f_even (n x : nat) : nat := n + x.
Definition f_odd (n x : nat) : nat := n * x.

(** Point-free: the body is an [if] whose branches are functions, and no
    argument is written. *)
Definition pick (n : nat) : nat -> nat :=
  if Nat.even n then f_even n else f_odd n.

Definition go (n m : nat) : nat := pick n m.

Crane Extraction "ternary_of_two_lambdas" go.
