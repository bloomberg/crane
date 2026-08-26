(* Regression: a multi-line [Prop] precondition is emitted as a single-line [//]
   comment, so everything after the first newline lands in the file as C++.

   Crane annotates the extracted function with its subset-type precondition:

     uint64_t Mod::head(const Sig<lst> &p) { // Precondition: match l with
       | Mod.nil = > False | Mod.cons _ _ = > True end assert(true);

   The Rocq term is pretty-printed across several lines, the [//] closes at
   the first one, and the remainder is parsed as code:

     error: expected expression
     error: use of undeclared identifier 'False'

   The comment must either be a block comment or have every line prefixed. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module SigSubset.
Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.
Definition nonempty (l : lst) : Prop := match l with nil => False | _ => True end.
Definition head (p : { l : lst | nonempty l }) : nat :=
  match proj1_sig p as x return nonempty x -> nat with
  | nil => fun h => match h with end
  | cons x _ => fun _ => x
  end (proj2_sig p).
Definition go : nat := head (exist _ (cons 7 nil) I).
End SigSubset.
Crane Extraction "sig_prop_comment" SigSubset.
