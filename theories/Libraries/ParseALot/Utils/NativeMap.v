(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import ZArith.

(** Axiomatized native finite-map interface, realized to [immer::map] at
    extraction (see [benchmarking/CraneExtraction.v]).

    This is a trusted extraction realization: the three spec axioms below are the
    trust boundary for the native container, in the same spirit as trusting
    [immer::flex_vector] to implement [list]. It replaces the hand-rolled binary
    [HashTrie.Trie] in the lexer memo (see [Lexer/Memo/ConcreteMemo.v]), which
    extracted to a functional [shared_ptr]-per-node C++ structure that dominated
    lexing time. Keying directly on the (integer) position avoids the per-access
    [list bool] serialization the trie required. *)
Module NativeMap.

  (** A persistent finite map from keys [K] to values [V]. *)
  Parameter t : Type -> Type -> Type.

  (** The empty map. *)
  Parameter empty : forall {K V}, t K V.

  (** Look up [k]; [None] if absent. *)
  Parameter get : forall {K V}, t K V -> K -> option V.

  (** Insert or overwrite [k |-> v]. *)
  Parameter set : forall {K V}, t K V -> K -> V -> t K V.

  (** Lookup in the empty map is always [None]. *)
  Axiom get_empty : forall K V k, get (@empty K V) k = None.

  (** Reading back a just-written key returns the stored value. *)
  Axiom get_set : forall K V (m : t K V) k v, get (set m k v) k = Some v.

  (** Writing key [k] does not affect lookup at a distinct key [k']. *)
  Axiom get_set_moot : forall K V (m : t K V) k k' v,
      k <> k' -> get (set m k v) k' = get m k'.

End NativeMap.
