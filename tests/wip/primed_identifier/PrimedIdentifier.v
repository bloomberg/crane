(** Crane bug: a Rocq identifier containing a prime is emitted verbatim into
    C++, where [']  is not an identifier character.

    Both a user definition ([twice']) and a Rocq-generated instance name
    ([Sized_nat'], from two instances of the same class on the same type) are
    affected.

    Expected: the prime is mangled, e.g. [twice_].
    Actual:   Nat twice'(const Nat& n)
              warning: missing terminating ' character
              error: expected ';' after top level declarator
              error: redefinition of 'twice'

    The generated file's layout also collapses from the prime onward --
    statements are jammed onto single lines -- so the pretty-printer is
    reading the [']  as an open quote too.

    Seen in Vellvm as [Traversal::TFunctor_list'(h4)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Sized (T : Set) := size : T -> nat.

#[global] Instance Sized_nat : Sized nat := fun n => n.
#[global] Instance Sized_nat' : Sized nat | 2 := fun n => S n.

Definition twice' (n : nat) : nat := n + n.

Module PrimedIdentifier.

  Definition use (n : nat) : nat := twice' (@size nat Sized_nat' n).

End PrimedIdentifier.

Crane Extraction "primed_identifier" PrimedIdentifier.
