(** Every inductive's C++ struct declares members of its own — [v], [v_],
    [v_mut], [clone] and [variant_t].  A user name that lands beside them in
    that struct must be renamed, but two spellings are not:

    - a constructor field named [clone] becomes a data member [clone] beside
      the generated [clone()], which C++ rejects as a redefinition;

    - an inductive named [clone] gives a struct [clone] whose generated
      [clone()] then reads as a constructor with a return type. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module GeneratedMemberNameCollision.
  Inductive boxed : Set := Box (clone : nat) (v_mut : nat).

  Definition unbox (b : boxed) : nat := match b with Box a b => a + b end.

  Inductive clone : Set := Dup : nat -> clone.

  Definition undup (c : clone) : nat := match c with Dup n => n end.

  Definition boxed_sum : nat := unbox (Box 1 2).
  Definition clone_val : nat := undup (Dup 4).
End GeneratedMemberNameCollision.

Crane Extraction "generated_member_name_collision" GeneratedMemberNameCollision.
