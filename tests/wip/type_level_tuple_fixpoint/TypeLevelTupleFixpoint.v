From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module TypeLevelTupleFixpoint.

(** A [Fixpoint] returning a [Type] built from tuples.  [tup 3] is a concrete
    nested [std::pair] at every use site, but Crane erases it to [std::any] and
    then reads through it:

      error: no viable conversion from returned value of type 'std::any'
             to function return type 'Nat'

    Unlike [type_level_fixpoint_call], the computed type is a *tuple*, not a
    function type. *)

Fixpoint tup (n : nat) : Type :=
  match n with O => unit | S k => (nat * tup k)%type end.

Definition mk3 : tup 3 := (1, (2, (3, tt))).

Definition fst3 (t : tup 3) : nat := fst t.

Definition run : nat := fst3 mk3.

End TypeLevelTupleFixpoint.

Crane Extraction "type_level_tuple_fixpoint" TypeLevelTupleFixpoint.run.
