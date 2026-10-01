From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import nested_owner_two_template_heads.A.
From CraneTestsRegression Require Import nested_owner_two_template_heads.Aux.

(** This file's name begins with the inductive's, so its functions are
    candidates to become methods of [bag]'s struct.  [p] is a function, which
    is what gives the method a template parameter of its own -- one the struct
    does not have, so the definition needs two [template] heads rather than one
    flattened list.  The body names [Tally.bump], which forces the definition
    out of the struct. *)
Fixpoint countIf {A : Set} (p : A -> bool) (b : bag A) : nat :=
  match b with
  | Empty => 0
  | Add x r => if p x then Tally.bump (countIf p r) else countIf p r
  end.
