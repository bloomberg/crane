From Crane Require Import Mapping.Std.

(** A polymorphic inductive at namespace scope.  Its wrapper holds nothing but
    the struct, so the two are written as one -- a [template <...> struct Box]
    with no enclosing name, which is the branch an out-of-line member's
    qualifier has to agree with. *)
Inductive box (A : Set) : Set := | Bx : A -> box A | Bnil : box A.

Arguments Bx {A} _.
Arguments Bnil {A}.

Definition raw_size {A : Set} (b : box A) : nat :=
  match b with Bx _ => 1 | Bnil => 0 end.
