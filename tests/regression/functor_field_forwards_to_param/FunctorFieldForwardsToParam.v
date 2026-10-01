(* A functor field that forwards to the same field of the functor's parameter
   is emitted as a call to itself.

   [Definition eq_dec := M.eq_dec] inside [Make (M : MINI)] becomes

     template <MINI M> struct Make {
       using t = typename M::t;
       static bool eq_dec(t x0_, t x1_) {
         return eq_dec(std::move(x0_), std::move(x1_));
       }
     };

   where the unqualified [eq_dec] finds the member being defined rather than
   [M::eq_dec].  The arguments are forwarded unchanged and nothing guards the
   call, so it is unconditional self-recursion: the binary overflows its stack
   on the first call.

   The reason to prefer this test to the error count is that there is no error.
   It compiles clean, and every other defect in this area stops a build; this
   one ships.  A qualifier is missing, and C++ resolves the unqualified name to
   something that exists, which is why nothing is diagnosed.

   The sibling [functor_value_field_call] shows the qualifier being written
   correctly for [C::zero], so the general mechanism works.  What distinguishes
   this case is that the functor's field and the parameter's field have the
   {e same name}, which is exactly when the missing qualifier stops being
   harmless.

   Vellvm: [AstLib.v:210], [Module Ident := Make_UDT(IdentDec)], where
   [Make_UDT] is the stdlib functor whose body forwards [eq_dec] to its
   parameter.  Generated at [vellvm_bench.h:2241]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module FunctorFieldForwardsToParam.

Module Type MINI.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End MINI.

Module BoolDec <: MINI.
  Definition t := bool.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof. decide equality. Defined.
End BoolDec.

(* Two fields forwarding to the same target, differing only in whether they
   share its name.  [eq_dec2] is the control: if it gets the [M::] qualifier
   and [eq_dec] does not, the shared name is the defect, and the comparison is
   inside one generated struct rather than across two tests. *)
Module Make (M : MINI) <: MINI.
  Include M.
  Definition eq_dec2 := eq_dec.
End Make.

(* Bound to a name that collides with nothing in scope, so that a defect
   reproducing here is a property of the functor application and not of the
   name it is bound to. *)
Module B := Make BoolDec.

Definition go (x y : B.t) : bool := if B.eq_dec x y then true else false.

Definition go2 (x y : B.t) : bool := if B.eq_dec2 x y then true else false.

End FunctorFieldForwardsToParam.

Crane Extraction "functor_field_forwards_to_param" FunctorFieldForwardsToParam.
