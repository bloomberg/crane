(** A validator for the MiniCpp IR.

    Crane's erasure invariants — which values are physically inside a
    [std::any], and at what shape they may be read back out — are decided at
    many sites across {!Translation}, {!Gen_decls} and {!Loopify}.  This module
    checks, at a pass boundary, the ones that were previously recorded only in
    comments, so that a disagreement between two of those sites is reported
    where it is introduced rather than as a [std::bad_any_cast] in a test
    binary.

    Enabled by the [CRANE_CHECK_IR] environment variable: unset or ["0"] is
    off, ["1"] reports each distinct violation once as a warning, and
    ["strict"] raises on the first one.  The test suite runs with ["1"].

    See [docs/nanopass-plan.md]. *)

(** [check ~where decl] validates [decl].  A no-op unless [CRANE_CHECK_IR] is
    set.  [where] names the pass that last touched the declaration and appears
    in the diagnostic, so a report points at the pass to look in. *)
val check : where:string -> Minicpp.cpp_decl -> unit
