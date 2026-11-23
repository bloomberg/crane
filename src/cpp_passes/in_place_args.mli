(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Arguments a callee writes or replaces in place (typed mappings: the
    replace form, or the write-through form [T&] of a mutable value).

    A generated function's parameter planned [By_reference]
    ({!Core_plan.Access}), and an operation mapping's argument the template
    receives as a mutable lvalue ({!Base.Mapping_operation.argument}'s
    [in_place]: a [Replace], or a write of a mutable value), bind only a
    mutable lvalue.  An argument there that is a variable the caller
    declares writable -- by value and not [const], or a reference to
    non-[const] -- is passed as it is, and the callee writes the caller's
    variable, as the access it planned says.  Anything else -- a call's
    result, a variable the caller only borrows or declares [const], a
    field of a matched value -- is materialised in a temporary
    ([crane::writable(e).ref()]), which the callee writes and the end of
    the full expression drops.

    The callee's positions are read from its callable plan
    ({!Core_plan.Callable_abi.modes}), not from the call's argument types,
    so a call lowered anywhere -- a direct call, a loop, a frame -- is
    covered once its arguments are final.  A pass of {!Pipeline}, after
    {!Shared_args}, whose temporaries are writable locals. *)

val transform_decl : Unit_plan.Context.t -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
