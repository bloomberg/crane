(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The declared view conversions at calls (typed mappings, design 7,
    12.7, 12.8).

    A generated function's parameter planned as a view
    ({!Cpp_ir.Param_mode.By_view}, read from its callable plan), and an
    operation mapping's argument whose template is given a view
    ({!Base.Mapping_operation.argument}'s [view]), take the view of the
    value the caller passes.  The caller converts what it holds with the
    mapping's declared conversions only:
    - a canonical value: [view_from_canonical];
    - a view of the same kind (its own view parameter, or a view an
      operation borrowed): as it is;
    - a writable view where a read view is taken: [read_from_write].

    A view an operation returns borrowed ([ReturnBorrowed ReadViewBorrow]
    or [WritableViewBorrow]) carries its owner's provenance: passed at once
    to a view position of an enclosing call, or bound ahead of it by
    {!Shared_args} and only passed so, it stays a view within its owner's
    lifetime; anywhere else -- returned, stored, passed canonically -- it
    escapes, and is materialised by its [MaterialiseView] construction, or
    refused when it is [BorrowOnly].

    A variable passed as a view beside an argument the callee may
    invalidate views of ({!Cpp_ir.Param_mode.t}'s [invalidates_views], an
    operation's [InvalidatesViews], a [Replace]) would hold a dangling
    view: a read view of a materialisable type is taken of a copy instead,
    anything else is refused.

    A pass of {!Pipeline}, after {!In_place_args}, before the operation
    templates are instantiated ([foreign]). *)

val transform_decl : Unit_plan.Context.t -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t

(** The copy of a read view of the mapped head [g], at the canonical
    type's arguments [types], that its [MaterialiseView] construction
    makes; [None] where the view is [BorrowOnly]. *)
val materialisable : Names.GlobRef.t -> (Cpp_ir.Lowered.Type.t list -> Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t) option
