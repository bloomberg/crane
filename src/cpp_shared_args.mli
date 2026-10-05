(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An argument a mapping splices more than once, evaluated once.

    A mapping's text is spliced, not called: [Nat.sub] maps to
    [((%a0 - %a1) > %a0 ? 0 : (%a0 - %a1))], so an argument it mentions twice
    is evaluated twice -- twice the work for a call, twice the effect for one
    with an effect, and for a recursive call in the argument, work exponential
    in the depth.  The source evaluates it once.  So such an argument, unless
    a second evaluation is free (a variable, a literal, a field of one), is
    bound to a local first -- [auto &&], which neither copies an lvalue nor
    loses a temporary -- and the mapping splices the local.

    The binding goes in front of the statement, so only a call that statement
    evaluates unconditionally, once, is rewritten: one under a conditional, a
    short-circuit or a loop's condition is left as written. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
