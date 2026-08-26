(* Regression: [nested_fix_loopify] where the inner [fix] captures a *function*
   parameter.

   [inner] applies [f], a parameter of the enclosing [walk].  All three kinds
   of capture in scope are lost at once -- the list, the closure and the
   accumulator:

     error: ... '!__is_same(std::shared_ptr<lst> &, ...)'
     error: ... '!__is_same((lambda at inner_fix_captures_fn.cpp:25:15) &, ...)'
     error: ... '!__is_same(unsigned long long &, unsigned long long &)'

   The closure case matters on its own: even once the value captures are
   fixed, a [std::function] parameter has to be captured by a mechanism that
   keeps it alive for the lifetime of the inner loop. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module InnerFixCapturesFn.
Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.
Fixpoint walk (f : nat -> nat) (l : lst) : nat :=
  match l with
  | nil => 0
  | cons x r =>
      (fix inner (m : lst) (a : nat) : nat :=
         match m with nil => a | cons y s => inner s (a + f y) end) r (f x)
      + walk f r
  end.
Fixpoint mk (n : nat) : lst := match n with O => nil | S m => cons 1 (mk m) end.
Definition go (n : nat) : nat := walk (fun k => k + 1) (mk n).
End InnerFixCapturesFn.
Crane Extraction "inner_fix_captures_fn" InnerFixCapturesFn.
