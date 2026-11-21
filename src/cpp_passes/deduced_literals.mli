(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** String literals where C++ deduces the type.

    A Rocq string literal ([Literal (String _)]) is printed as the C++
    string literal, a character array, which converts to the mapped string
    type wherever that type is the one expected: a declared variable, a
    parameter, a declared return type.  Where C++ deduces the type from the
    expression instead -- a [return] in a lambda without a declared return
    type, an [auto] variable -- it would deduce [const char*]: the lambda's
    other returns of the string type then disagree with it, and a value
    converted from it again (a [crane::field] of the string) needs two user
    conversions.  There the literal is constructed as the mapped type's
    canonical object.  A literal taken as a read view is {!View_args}'s.

    A pass of {!Pipeline}, after {!View_args}. *)

val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
