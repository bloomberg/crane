(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Native compiler integration shared by extraction tests and benchmarks.

    The module constructs compiler argument vectors and delegates execution to
    {!Subprocess}, so source names, include directories, and flags are never
    interpolated into a shell command. C++ compilation follows Crane's selected
    standard-library mode, including BDE-specific includes and libraries. *)

(** Raised when [clang++] cannot be found on [PATH]. *)
exception NoClangFound

(** [ClangError (code, diagnostics)] reports a non-zero Clang termination code
    and the compiler's captured stderr. *)
exception ClangError of int * string

(** Raised when [ocamlopt] cannot be found on [PATH]. *)
exception NoOcamloptFound

(** [OcamloptError (code, diagnostics)] reports a non-zero OCaml compiler
    termination code and the compiler's captured stderr. *)
exception OcamloptError of int * string

(** [compile_cpp ?shouldlink ?includes ?flags ?outfile ?errfile infile]
    compiles [infile] with [clang++]. By default it emits an object file next to
    [infile]; [shouldlink = true] instead links an executable. [includes] become
    individual [-I] arguments and [flags] are forwarded verbatim as argv
    elements. [outfile] overrides the derived destination. [errfile] optionally
    selects the temporary diagnostics file, which is removed before returning.

    @raise NoClangFound when [clang++] is unavailable
    @raise ClangError when compilation or linking fails *)
val compile_cpp :
  ?shouldlink:bool ->
  ?includes:string list ->
  ?flags:string list ->
  ?outfile:string ->
  ?errfile:string ->
  string ->
  unit

(** [compile_ocaml ?shouldlink ?includes ?flags ?outfile ?errfile infile]
    compiles [infile] through [ocamlfind ocamlopt]. By default it performs
    compilation only; [shouldlink = true] links an executable with the Rocq
    runtime. Include directories and flags are supplied as discrete argv
    elements, and [outfile] overrides the derived destination.

    @raise NoOcamloptFound when [ocamlopt] is unavailable
    @raise OcamloptError when compilation or linking fails *)
val compile_ocaml :
  ?shouldlink:bool ->
  ?includes:string list ->
  ?flags:string list ->
  ?outfile:string ->
  ?errfile:string ->
  string ->
  unit

(** [compile_and_test ?outfile ?errfile infile] links the object corresponding
    to extracted C++ source [infile] with the adjacent [.t.cpp] driver, executes
    the resulting test program, and returns its stdout followed by stderr.

    @raise NoClangFound when [clang++] is unavailable
    @raise ClangError when the test executable cannot be linked
    @raise Failure when the test executable exits unsuccessfully *)
val compile_and_test :
  ?outfile:string -> ?errfile:string -> string -> string
