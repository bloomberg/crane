(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Boundary checks on Core as it leaves extraction and the Core passes, run
    under [CRANE_CHECK_IR] as the last of those passes ([core_passes] in
    [extract_env.ml]), before {!Phase.freeze}: every global use carries a
    well-formed instantiation of its callee's own type scheme, and every
    match branch returns the inductive its result type names.  Without
    [CRANE_CHECK_IR] it does nothing. *)

(** Checks every global use in the structure: no proof placeholder among
    its written arguments; an instantiation at the callee's own scheme, with
    one slot per variable by construction, holding no metavariable; and each
    hole held by one use, or by copies of that whole use.  Checks every
    match branch whose result type names an inductive: a construction, a
    numeral, or an inner match's branch it ends in names the same one (a
    simplification that moved the branch's value kept its old type
    otherwise).  A violation is an extraction error naming the callee or
    the two types, and the invariant. *)
val structure : 'p Core.Program.at -> unit
