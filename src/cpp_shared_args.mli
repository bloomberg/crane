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
    short-circuit or a loop's condition is left as written.

    A pass of {!Cpp_pipeline}: it runs after the temporaries Normalize named
    go back where they are read, so that none of them is put back into the
    text that repeats it. *)

(** [transform_decl d] is [d] with each repeated argument of every
    statement's unconditional calls bound once, to a fresh [_onceN] local:
    one no body of [d] visited so far declares or reads.  A function's own
    body is visited before anything nested in it, and a parameter its body
    does not read is written unnamed, so nothing in scope at the binding
    shares its name. *)
val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
