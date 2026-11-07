(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The moves a [return] writes: none where C++ moves the returned value on
    its own.  Every other move is decided over Core
    ({!Ownership_ir}) or made as control is lowered. *)

open Minicpp

val drop_return_moves : cpp_decl -> cpp_decl
(** Remove the [std::move] around the value of every [return] that moves it
    anyway -- a call, a construction, or a by-value local or parameter of the
    innermost function -- where writing it would only suppress copy elision.
    A returned structured binding, reference, loop variable or lambda capture
    keeps its move: C++ copies those.  This is where a returned value's move
    is spelled, rather than in the printer. *)
