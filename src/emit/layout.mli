(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Layout of generated C++ source: the printer's token stream indented,
    broken into lines of at most {!column_limit} columns and spaced with
    blank lines in the LLVM style, as clang-format lays it out with
    [SeparateDefinitionBlocks: Always].  Pure: text in, text out. *)

(** The width lines are broken to fit. *)
val column_limit : int

(** [layout ~file text] lays out the C++ source [text].  [file] is the name
    of the file it is written to, if any: an implementation file includes
    its own header first. *)
val layout : ?file:string -> string -> string
