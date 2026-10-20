(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** No local is read after it is moved (docs/Pipeline-Disentangling-Plan.md,
    section 4.10: "a moved local is not subsequently read on the same control
    path").

    The moves a body holds come from several places -- translation at the
    last uses its region's plan finds ({!Ownership_plan}), Loopify's frames
    and loops, {!Last_use}, the depth flattening -- and this checks all of
    them against the C++ they ended up in, independently of how each was
    decided.  A move reaches a whole local or one member of it; a later read
    of the same local, or of the same member, is a violation, and so is a
    read beside it in an expression whose parts C++ evaluates in no fixed
    order.  An assignment gives a local, or a member, a new value; a [return]
    or a [throw] ends the path; a loop's body is followed by its head; the
    arms of a conditional are alternatives.  A closure reads what it closes
    over where it is made, and its own body is checked as a body.  A body
    holding raw C++ is not checked.

    Under [CRANE_CHECK_IR] each violation is reported ({!Probe.violation}). *)

val check_decl : Minicpp.cpp_decl -> unit
