(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** WIP: A list of Fixpoint-computed tuples (symbols_semty) has
    element type erased to std::any.  Accessing tuple components
    of list elements (e.g. fst on the head) generates .first on
    std::any, which fails to compile. *)
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

Module ListCollect (Ty : SymTypes).
  Definition symbols_semty (gamma : list Ty.sym) : Type :=
    tuple (List.map Ty.sym_semty gamma).

  Definition collect
    (x : Ty.sym) (xs : list Ty.sym)
    (n : nat) (default : symbols_semty (x :: xs))
    : list (symbols_semty (x :: xs)) :=
    let fix go (n : nat) (acc : list (symbols_semty (x :: xs))) :=
      match n with
      | O => acc
      | S n' => go n' (default :: acc)
      end
    in go n nil.

  Definition head_first
    (x : Ty.sym) (xs : list Ty.sym)
    (l : list (symbols_semty (x :: xs)))
    (default : Ty.sym_semty x)
    : Ty.sym_semty x :=
    match l with
    | nil => default
    | vs :: _ => fst vs
    end.

  Definition collect_and_get_first
    (x : Ty.sym) (xs : list Ty.sym)
    (n : nat)
    (default_tuple : symbols_semty (x :: xs))
    (default_val : Ty.sym_semty x)
    : Ty.sym_semty x :=
    head_first x xs (collect x xs n default_tuple) default_val.
End ListCollect.

Crane Separate Extraction ListCollect.
