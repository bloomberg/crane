(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Mapped identities held in a local (Descriptor.v, [LocalStorage]).

    A variable bound to a fresh identity -- an operation whose result is
    [ReturnFreshIdentity] with one component initialised once from an
    argument -- of a mapped type declaring [LocalStorage], every later use
    of which is the operand of one of its view conversions outside any
    lambda, holds the component by value: [A x = v;] in place of the
    canonical owner, each view of it spelled by [local_view].  It is never
    passed as the canonical value, returned, stored or captured, so nothing
    outlives the scope that declares it.

    A pass of {!Pipeline}, after {!View_args}. *)

val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
