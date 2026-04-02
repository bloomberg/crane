(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Axiomatized [std::string_view] interface with verification axioms.

    Provides non-owning string views with [substr], [contains], [length],
    and character access, plus axioms relating these operations for use
    in verified programs. *)
From Corelib Require Import PrimString PrimInt63.
From Corelib Require Import Relations.Relation_Definitions.

Open Scope int63.

Axiom string_view : Type.
Axiom empty : string_view -> bool.
Axiom empty_sv : string_view.
Axiom sv_eq : string_view -> string_view -> bool.
Axiom length : string_view -> int.
Axiom substr : string_view -> int -> int -> string_view.
Axiom sv_get : string_view -> int -> char63.
Axiom sv_at : string_view -> int -> char63.
Axiom sv_of_string : string -> string_view.
Axiom contains : string_view -> char63 -> bool.


Definition sv_eq_rel : relation string_view := fun sv1 sv2 => eq_true (sv_eq sv1 sv2).

Axiom sv_eq_rel_equiv : equivalence string_view sv_eq_rel.
Axiom empty_substr : forall sv i, empty (substr sv i 0) = true.
Axiom empty_length : forall sv, empty sv = true <-> length sv = 0.
Axiom length_of_string : forall s, length (sv_of_string s) = PrimString.length s.
Axiom substr_of_string_comm : forall s i j, compare i j <> Gt
                              -> compare j (PrimString.length s) <> Gt
                              -> substr (sv_of_string s) i (sub j i) = sv_of_string (PrimString.sub s i j).

(* Axioms relating contains, sv_get, substr, and length *)

(* A string_view contains a character iff that character appears at some valid position *)
Axiom contains_iff_exists_get : forall sv c,
  contains sv c = true <-> exists i, leb 0 i = true /\ ltb i (length sv) = true /\ sv_get sv i = c.

(* Characters in a prefix substr are exactly those in the corresponding positions of the original *)
Axiom sv_get_substr : forall sv start len i,
  leb 0 i = true -> ltb i len = true -> ltb (add start i) (length sv) = true ->
  sv_get (substr sv start len) i = sv_get sv (add start i).

(* Length of a substr is bounded by the requested length *)
Axiom length_substr : forall sv start len,
  leb 0 start = true -> leb 0 len = true ->
  length (substr sv start len) = if ltb (add start len) (length sv)
                                  then len
                                  else if leb start (length sv)
                                       then sub (length sv) start
                                       else 0.

(* Simpler axiom for prefix case: length of substr from 0 *)
Axiom length_substr_prefix : forall sv len,
  leb 0 len = true -> leb len (length sv) = true ->
  length (substr sv 0 len) = len.

(* Key axiom: if no position in [0, n) contains a character c, then contains returns false *)
Axiom contains_substr_prefix_false : forall sv n c,
  leb 0 n = true -> leb n (length sv) = true ->
  (forall i, leb 0 i = true -> ltb i n = true -> sv_get sv i <> c) ->
  contains (substr sv 0 n) c = false.

(* Conversely, if some position contains c, then contains returns true *)
Axiom contains_substr_prefix_true : forall sv n c i,
  leb 0 n = true -> leb n (length sv) = true ->
  leb 0 i = true -> ltb i n = true -> sv_get sv i = c ->
  contains (substr sv 0 n) c = true.

(* Non-negative length *)
Axiom length_nonneg : forall sv, leb 0 (length sv) = true.

Require Crane.Extraction.

Crane Extract Inlined Constant string_view => "std::basic_string_view<char>" From "string_view".
Crane Extract Inlined Constant empty => "%a0.empty()" From "string_view".
Crane Extract Inlined Constant sv_eq => "%a0 == %a1" From "string_view".
Crane Extract Inlined Constant length => "%a0.length()" From "string_view".
Crane Extract Inlined Constant substr => "%a0.substr(%a1, %a2)" From "string_view".
Crane Extract Inlined Constant sv_of_string => "{%a0.data(), %a0.size()}" From "string_view".
Crane Extract Inlined Constant contains => "%a0.contains(%a1)" From "string_view".
Crane Extract Inlined Constant sv_get => "%a0[%a1]" From "string_view".
Crane Extract Inlined Constant sv_at => "%a0.at(%a1)" From "string_view".
Crane Extract Inlined Constant empty_sv => "std::string_view(nullptr, 0)" From "string_view".
