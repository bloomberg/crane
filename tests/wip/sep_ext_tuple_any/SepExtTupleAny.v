From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | nil => unit
  | cons x xs' => prod x (tuple xs')
  end.

Module Type SymTypes.
  Parameter symbol : Type.
  Parameter symbol_semty : symbol -> Type.
End SymTypes.

Module Defs (Ty : SymTypes).
  Definition symbols_semty (gamma : list Ty.symbol) : Type :=
    tuple (List.map Ty.symbol_semty gamma).

  Definition get_first
    (x : Ty.symbol) (xs : list Ty.symbol)
    (vs : symbols_semty (x :: xs))
    : Ty.symbol_semty x :=
    fst vs.
End Defs.

Crane Separate Extraction Defs.
