From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module TypeValuedIfEliminator.

(** [sel] computes a [Type] by a [bool] test.  Crane erases [sel b] to
    [std::any] but keeps the branch bodies typed against the concrete types,
    so both branches of the dependent eliminator are ill-typed:

      error: no viable conversion from returned value of type 'sel'
             (aka 'std::any') to function return type 'Nat'
      error: no member named 'length' in 'std::any' *)

Definition sel (b : bool) : Type := if b then nat else list nat.

Definition zero (b : bool) : sel b :=
  match b with true => 0 | false => nil end.

Definition size (b : bool) (x : sel b) : nat :=
  match b return sel b -> nat with
  | true => fun n => n
  | false => fun l => List.length l
  end x.

Definition run : nat := size true (zero true).

End TypeValuedIfEliminator.

Crane Extraction "type_valued_if_eliminator" TypeValuedIfEliminator.run TypeValuedIfEliminator.size TypeValuedIfEliminator.zero.
