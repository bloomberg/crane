(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A short, ordered list of small local simplifications, each independent
    and each removing something:

    - A declared operation whose mapping guards a case the context rules out
      becomes the language's own operator: a division or remainder by a
      nonzero numeral, and a truncated subtraction [a - b] where a fact of
      the enclosing branch gives [b <= a] -- [if (b <= a) ... a - b ...],
      [if (n == 0) ... else ... n - 1 ...].  Only at a width the language
      does not promote ({!Minicpp.Bsub}).  A fact holds in the branch its
      condition dominates, about variables that branch neither assigns nor
      redeclares; it does not cross into a lambda, which runs elsewhere.
    - A condition that is a literal selects its branch.
    - [if (c) return true; else return false;] returns [c], for a [c] that
      is a [bool].
    - A binding of a pure value nothing reads is dropped.

    Effects, evaluation counts and the fixed-width arithmetic of every
    operation are kept: an operation is rewritten only to what its declared
    meaning says it computes in that context. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
