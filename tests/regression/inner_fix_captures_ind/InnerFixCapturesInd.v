(* Regression: [nested_fix_loopify] where the inner [fix] captures an *inductive*
   binder rather than a [nat].

   [inner] calls [len r], with [r] bound by the enclosing [cons _ r] pattern.
   The capture is dropped and replaced by a placeholder:

     error: static assertion failed due to requirement
            '!__is_same(std::shared_ptr<lst> &, std::shared_ptr<lst> &)':
            std::declval can only be used in an unevaluated context

   Separate from the [nat] case because the inductive capture goes through the
   shared_ptr field path. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module InnerFixCapturesInd.
Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.
Fixpoint len (l : lst) : nat := match l with nil => 0 | cons _ r => S (len r) end.
Fixpoint outer (l : lst) : nat :=
  match l with
  | nil => 0
  | cons _ r =>
      (fix inner (m : lst) (a : nat) : nat :=
         match m with nil => a | cons _ s => inner s (a + len r) end) r 0
      + outer r
  end.
Fixpoint mk (n : nat) : lst := match n with O => nil | S m => cons 1 (mk m) end.
Definition go (n : nat) : nat := outer (mk n).
End InnerFixCapturesInd.
Crane Extraction "inner_fix_captures_ind" InnerFixCapturesInd.
