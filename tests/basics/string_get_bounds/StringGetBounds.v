(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Boundary regression for checked string / string-view indexing.

    Rocq's [PrimString.get] is total: [get_spec] gives
    [get s i = nth (to_nat i) s 0], so an out-of-range index yields the null
    char rather than undefined behavior. The extraction must reproduce that
    (a bounds check), never an unchecked [operator[]]. Covers security-scan
    findings 21 (PrimString.get) and 23 (StringView.sv_get) for the std flavor. *)
Require Import PrimString PrimInt63.
From Crane Require Import Extraction Mapping.Std External.StringViewStd.

Open Scope pstring_scope.
Open Scope int63.

Module StringGetBounds.

Definition s : string := "abc".

(** In-bounds access returns the expected character. *)
Definition first : char63 := PrimString.get s 0.

(** Out-of-range access returns the null char (Rocq semantics), not an
    out-of-bounds read. *)
Definition oob : char63 := PrimString.get s 100.

Definition sv : string_view := sv_of_string s.

(** Same contract for string views. *)
Definition sv_first : char63 := sv_get sv 0.
Definition sv_oob : char63 := sv_get sv 100.

End StringGetBounds.

Crane Extraction "string_get_bounds" StringGetBounds.
