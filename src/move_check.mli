(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** No local is read after it is moved: a moved local is not read again on
    the same control path.  A validator of OwnershipIR's decisions, run over
    the finished MiniCpp of each declaration.

    The moves a body holds come from several places -- translation at the
    last uses its region's plan finds ({!Ownership_ir}), Loopify's frames
    and loops, the depth flattening -- and this checks all of
    them against the C++ they ended up in, independently of how each was
    decided.  A move reaches a whole local or one member of it -- a field
    of the alternative its variant holds among them; a later read of the
    same local, or of the same member, is a violation, and so is a read
    beside it in an expression whose parts C++ evaluates in no fixed order;
    a braced initialiser evaluates its elements in order.  A reference
    bound into a local -- a structured binding, a match's field or
    alternative, a declared reference -- reads and moves the part of the
    local it names: a move of the local is a move of every such part, so a
    read through the reference after it is a violation, and so is a read of
    the whole after a part is moved out through one.
    A method is called on the whole local.  A reuse arm's token is checked
    as a linear one, used exactly once: the reuse factory it is handed to
    consumes the token's storage, which nothing may read or consume again,
    though what the arm moved out of the local before is not read of it.  An assignment gives a local, or a member, a new value; a [return]
    or a [throw] ends the path; a loop's body is followed by its head; the
    arms of a conditional are alternatives.  A closure reads what it closes
    over where it is made, and its own body is checked as a body.  A body
    holding raw C++ is not checked.

    A planned function's or method's parameters are checked against the
    convention its callable plan states ({!convention_violations}), and the
    lambda of each local fixpoint in its body -- its parameters other than
    the members it calls through -- against its function's
    ({!Ownership_ir.Local_passing}).  A local fixpoint lambda whose plan
    captures by reference ({!Ownership_ir.Local_captures}) must be written
    capturing by reference and must not escape the block that binds it.

    Under [CRANE_CHECK_IR] each violation is reported ({!Probe.violation}). *)

(** Check every function and method body of a declaration, nested
    namespaces, templates and structs included, and report each violation
    of the rules above. *)
val check_decl : Minicpp.cpp_decl -> unit

(** The locals [ss], a body, reads after it moves them, the backend's own
    storage aside. *)
val moved_reads : Minicpp.cpp_stmt list -> Names.Id.t list

(** The references [ss], a body, reads after the local each was bound into
    is given a new value, each with that local, since a borrowed value must
    not outlive the region it borrows from: the storage a reference names is
    destroyed or replaced by an assignment to the local holding it.  A
    pointer local given a new value leaves what it pointed at as it was. *)
val stale_references : Minicpp.cpp_stmt list -> (Names.Id.t * Names.Id.t) list

(** [convention_violations r params body]: what the parameters [params] of
    the callable [r], in declaration order, and its [body] contradict of the
    convention its callable plan states ({!Callable_abi.passing}), [None]
    where no plan states one.  The plan passes each parameter one way: a
    deduced callable forwarded exactly where the declaration is an [F &&],
    one it owns declared by value, and none it lends by reference moved out
    of by name -- the ownership plan moves only what the convention hands
    the body (a name the body declares again, as a frame handler binds a
    parameter's to the frame's field, is that local's). *)
val convention_violations :
  Names.GlobRef.t -> (Names.Id.t * Minicpp.cpp_type) list -> Minicpp.cpp_stmt list -> string list option
