(** A record field whose type is rank-2 polymorphic ([forall A B, ...]).

    Crane emits the field initialiser as a generic lambda but prints the body
    with the raw Rocq names instead of the translated ones:

    {v
      no template named 'list'; did you mean 'List'?
      use of undeclared identifier 'map'
    v} *)

Require Crane.Extraction.
Require Import List.

Module PolyRank2RecordField.

Record mapper := { run : forall A B : Type, (A -> B) -> list A -> list B }.

Definition m : mapper := {| run := fun A B f l => map f l |}.

Definition test1 (l : list nat) : list bool := run m nat bool (fun x => Nat.eqb x 0) l.
Definition test2 (l : list bool) : list nat := run m bool nat (fun b => if b then 1 else 0) l.

End PolyRank2RecordField.

Crane Extraction "poly_rank2_record_field" PolyRank2RecordField.
