(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A move of a local whose value is copied as its bits is the local.

    Lowering moves a local at its last use without asking what it holds: a
    loop's result ([_result = std::move(x);]), a frame's saved local, an
    argument named once ahead of a mapping's text.  For a value copied bit
    for bit -- a scalar, a pointer, an enumeration, a typed mapping's
    [BitCopy] type -- a move is a copy, and [std::move] only says otherwise.

    A local's type is the one it is declared at in scope: a parameter's, a
    variable's, or the type lowering recorded for an [auto] variable's
    value.  Where no such type is known, as for a match's bindings, the
    move stays.

    A pass of {!Pipeline}, after the returned moves are dropped. *)

(** Whether a value of type [t] is copied as its bits: a builtin scalar, a
    pointer, an enumeration, a typed mapping's [BitCopy] type or a type a
    legacy mapping spells as a scalar, or one of these [const] or behind a
    [const] reference. *)
val bit_copied : Cpp_ir.Lowered.Type.t -> bool

val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
