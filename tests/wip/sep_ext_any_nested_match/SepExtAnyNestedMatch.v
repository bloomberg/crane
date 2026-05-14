(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** WIP: Pattern-matching on a nested tuple whose component types are
    erased generates a double-cast: the inner any_cast uses the
    concrete Rocq type (pair<A, pair<B, unit>>) but the runtime value
    is pair<std::any, std::any>.  Extends sep_ext_tuple_any to cover
    nested destructuring (fst (snd vs)) rather than just fst. *)
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

Module Destruct (Ty : SymTypes).
  Definition symbols_semty (gamma : list Ty.sym) : Type :=
    tuple (List.map Ty.sym_semty gamma).

  Definition get_second
    (x y : Ty.sym) (rest : list Ty.sym)
    (vs : symbols_semty (x :: y :: rest))
    : Ty.sym_semty y :=
    fst (snd vs).
End Destruct.

Crane Separate Extraction Destruct.
