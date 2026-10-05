(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A short, ordered list of small local simplifications, each independent
    and each removing something:

    - A condition that is a literal selects its branch.
    - [if (c) return true; else return false;] returns [c], for a [c] that
      is a comparison or a connective, and so a [bool].
    - A binding of a pure value nothing reads is dropped.

    Effects and evaluation counts are kept: a mapped constant is never pure,
    so nothing its text might do is removed. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
