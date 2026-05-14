(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** WIP: When a function type is computed by a Fixpoint (via
    symbols_semty) and stored in a sigT, retrieving it with projT2
    yields std::any.  Crane either generates a "throw logic_error"
    stub or code that calls std::any as a function. *)
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
  Parameter sym : Type.
  Parameter sym_semty : sym -> Type.
End SymTypes.

Module Actions (Ty : SymTypes).
  Definition symbols_semty (gamma : list Ty.sym) : Type :=
    tuple (List.map Ty.sym_semty gamma).

  Definition entry : Type :=
    { gamma : list Ty.sym & symbols_semty gamma -> bool }.

  Definition make_entry
    (gamma : list Ty.sym) (f : symbols_semty gamma -> bool) : entry :=
    existT _ gamma f.

  Definition apply_entry (e : entry) (vs : symbols_semty (projT1 e)) : bool :=
    (projT2 e) vs.
End Actions.

Crane Separate Extraction Actions.
