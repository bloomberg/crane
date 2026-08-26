(* Regression: an inner [fix] that captures a variable from the enclosing match loses
   the capture, and Crane emits [std::declval] in its place.

   [inner] refers to [x], bound by the outer [cons x r] pattern.  The
   generated body substitutes a placeholder instead of the captured binder:

     inner( *(std::declval<std::shared_ptr<lst> &>()), (a + (a2 * std::declval<uint64_t &>())))

     error: static assertion failed ...
            std::declval can only be used in an unevaluated context

   [declval] is a type-level-only construct; reaching codegen means the free
   variables of the inner fixpoint were never resolved to real bindings.
   See [inner_fix_captures_ind] and [inner_fix_captures_fn] for the same
   failure with captures of other sorts. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module NestedFixLoopify.
Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.
Fixpoint outer (l : lst) : nat :=
  match l with
  | nil => 0
  | cons x r =>
      (fix inner (m : lst) (a : nat) : nat :=
         match m with nil => a | cons y s => inner s (a + y * x) end) r 0
      + outer r
  end.
Fixpoint mk (n : nat) : lst := match n with O => nil | S m => cons 2 (mk m) end.
Definition go (n : nat) : nat := outer (mk n).
End NestedFixLoopify.
Crane Extraction "nested_fix_loopify" NestedFixLoopify.
