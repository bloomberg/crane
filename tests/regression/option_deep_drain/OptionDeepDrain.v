(* Regression: recursion nested inside [option] gets no iterative drain.

   [Link : nat -> option chain -> chain] stores the tail as
   [shared_ptr<optional<chain>>].  [option] is a custom-extracted type, so the
   drain classifier does not recognise it as a mediating wrapper and emits no
   worklist destructor: ~chain -> ~Link -> ~shared_ptr -> ~optional -> ~chain.

   Distinct from tests/regression/option_nested_recursion_bad_cpp, which is a
   compile error in the match template; this one compiles and then dies at
   300k levels. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module OptionDeepDrain.
Inductive chain : Type := Link : nat -> option chain -> chain.
Fixpoint build (n : nat) (acc : chain) : chain :=
  match n with O => acc | S m => build m (Link n (Some acc)) end.
Definition go (n : nat) : nat := match build n (Link 0 None) with Link x _ => x end.
End OptionDeepDrain.
Crane Extraction "option_deep_drain" OptionDeepDrain.
