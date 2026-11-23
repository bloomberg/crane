(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An argument a mapping splices more than once, evaluated once.

    A mapping's text is spliced, not called: [Nat.sub] maps to
    [((%a0 - %a1) > %a0 ? 0 : (%a0 - %a1))], so an argument it mentions twice
    is evaluated twice -- twice the work for a call, twice the effect for one
    with an effect, and for a recursive call in the argument, work exponential
    in the depth.  The source evaluates it once.  So such an argument, unless
    a second evaluation is free (a variable, a literal, a field of one), is
    bound to a local first, and the mapping splices the local.  The local is
    an [auto &&] only where the argument names an object that outlives the
    statement (a variable, a member, a move of one); any other argument is a
    computation, which may return a reference into its own temporaries
    ([std::max(b, 1)], or any mapping's text) that a reference would
    outlive, so it is bound by value.  A prvalue initialises it in place.

    The binding goes in front of the statement, so only a call that statement
    evaluates unconditionally, once, is rewritten: one under a conditional, a
    short-circuit or a loop's condition is left as written.

    An operation mapping ({!Base.Mapping_operation}) is stricter (design
    11.9): every argument is evaluated once, in source order, before its
    text, whatever the text does with it.  Unless at most one argument
    computes anything and the text splices that one once, each argument that
    is not free to repeat is bound ahead of the call, in order; one the text
    does not splice (an [Ignore] argument) is evaluated as a statement and
    discarded.  The text-based counting above is not consulted for it.
    An argument bound by value and spliced once is passed as a move of its
    temporary, except one the text writes or replaces in place
    ({!Base.Mapping_operation.argument}'s [in_place]), which binds the
    temporary as an lvalue.

    A pass of {!Pipeline}: it runs after the temporaries Normalize named
    go back where they are read, so that none of them is put back into the
    text that repeats it. *)

(** [transform_decl d] is [d] with each repeated argument of every
    statement's unconditional calls bound once, to a fresh [_onceN] local:
    one no body of [d] visited so far declares or reads.  A function's own
    body is visited before anything nested in it, and a parameter its body
    does not read is written unnamed, so nothing in scope at the binding
    shares its name. *)
val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
