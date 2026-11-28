(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Axiomatized string view interface with verification axioms.

    Provides non-owning string views with [substr], [contains], [length],
    and character access, plus axioms relating these operations for use
    in verified programs.

    Flavor files ([StringView.v], [StringViewBDE.v]) re-export this
    module and add flavor-specific C++ extraction mappings. *)
From Corelib Require Import PrimString PrimInt63.
From Corelib Require Import Relations.Relation_Definitions.

Open Scope int63.

(** A non-owning, read-only view of characters: [std::string_view] or
    [bsl::string_view], by flavour. *)
Axiom string_view : Type.
(** Whether the view has no characters. *)
Axiom empty : string_view -> bool.
(** The empty view, over no storage. *)
Axiom empty_sv : string_view.
(** Equality of the viewed characters, not of the underlying buffers. *)
Axiom sv_eq : string_view -> string_view -> bool.
(** The number of viewed characters. *)
Axiom length : string_view -> int.
(** [substr sv start len]: at most [len] characters from [start]; total, an
    out-of-range [start] giving the empty view ([length_substr]). *)
Axiom substr : string_view -> int -> int -> string_view.
(** The character at an index; specified only in range (the C++ gives 0
    outside it). *)
Axiom sv_get : string_view -> int -> char63.
(** The character at an index, bounds-checked: the C++ [at] throws
    [std::out_of_range] outside the view. *)
Axiom sv_at : string_view -> int -> char63.
(** [sv_of_string] returns a NON-OWNING view: both the std and BDE mappings build
   it from the source string's [data()]/[size()], so the returned view is only
   valid while that source string is alive.  This is an inherent property of
   [string_view] and cannot be enforced at the mapping level (a temporary and an
   lvalue string share the same extraction template).  Callers MUST apply it to a
   string that outlives the view -- never to a temporary such as the result of a
   substring, concatenation, or function return -- or later reads through the
   view are use-after-free (CWE-416).  When a temporary source is unavoidable,
   bind it to a named [string] first, or keep the owning [string] and index into
   it rather than converting to a view. *)
Axiom sv_of_string : string -> string_view.
(** Whether some viewed character is [c]. *)
Axiom contains : string_view -> char63 -> bool.


(** [sv_eq] as a relation, to state that it is an equivalence. *)
Definition sv_eq_rel : relation string_view := fun sv1 sv2 => eq_true (sv_eq sv1 sv2).

(** Content equality is an equivalence. *)
Axiom sv_eq_rel_equiv : equivalence string_view sv_eq_rel.
(** A slice of length 0 is empty. *)
Axiom empty_substr : forall sv i, empty (substr sv i 0) = true.
(** Empty means length 0. *)
Axiom empty_length : forall sv, empty sv = true <-> length sv = 0.
(** A view of a string has the string's length. *)
Axiom length_of_string : forall s, length (sv_of_string s) = PrimString.length s.
(** Slicing commutes with viewing.  [i] and [j] are the start and end of a
    half-open slice, so both sides have length [sub j i]: [PrimString.sub]
    takes an offset and a length, and passing [j] as the length would make
    the primitive side longer than the view side (CWE-682 / CWE-345). *)
Axiom substr_of_string_comm : forall s i j, compare i j <> Gt
                              -> compare j (PrimString.length s) <> Gt
                              -> substr (sv_of_string s) i (sub j i) = sv_of_string (PrimString.sub s i (sub j i)).

(* Axioms relating contains, sv_get, substr, and length *)

(** A view contains [c] iff [c] is at some position in range. *)
Axiom contains_iff_exists_get : forall sv c,
  contains sv c = true <-> exists i, leb 0 i = true /\ ltb i (length sv) = true /\ sv_get sv i = c.

(** A slice's characters are the original's, shifted by [start]. *)
Axiom sv_get_substr : forall sv start len i,
  leb 0 i = true -> ltb i len = true -> ltb (add start i) (length sv) = true ->
  sv_get (substr sv start len) i = sv_get sv (add start i).

(** A slice has length [len] where it fits, else what remains after
    [start], else 0: [substr] clamps rather than fails. *)
Axiom length_substr : forall sv start len,
  leb 0 start = true -> leb 0 len = true ->
  length (substr sv start len) = if ltb (add start len) (length sv)
                                  then len
                                  else if leb start (length sv)
                                       then sub (length sv) start
                                       else 0.

(** A prefix within bounds has exactly the requested length. *)
Axiom length_substr_prefix : forall sv len,
  leb 0 len = true -> leb len (length sv) = true ->
  length (substr sv 0 len) = len.

(** A prefix of length [n] lacks [c] if none of its [n] positions holds [c]. *)
Axiom contains_substr_prefix_false : forall sv n c,
  leb 0 n = true -> leb n (length sv) = true ->
  (forall i, leb 0 i = true -> ltb i n = true -> sv_get sv i <> c) ->
  contains (substr sv 0 n) c = false.

(** Conversely, a prefix contains [c] if one of its positions holds [c]. *)
Axiom contains_substr_prefix_true : forall sv n c i,
  leb 0 n = true -> leb n (length sv) = true ->
  leb 0 i = true -> ltb i n = true -> sv_get sv i = c ->
  contains (substr sv 0 n) c = true.

(** A length is non-negative. *)
Axiom length_nonneg : forall sv, leb 0 (length sv) = true.
