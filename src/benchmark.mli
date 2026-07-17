(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Orchestration for the [Crane Benchmark] command.

    A benchmark request is a Cartesian product of Rocq definitions and compiler
    configurations. Crane extracts each definition automatically for every
    requested backend. Before invoking Hyperfine, every generated executable is
    run once and its output is compared with the first executable's output. *)

open Libnames

(** A native backend supported by the benchmark command. *)
type backend =
  | OCaml  (** Rocq's built-in OCaml extraction followed by [ocamlopt]. *)
  | Cpp  (** Crane's C++ extraction followed by [clang++]. *)

(** A Rocq definition participating in a benchmark comparison. *)
type subject = {
  term : qualid;  (** Definition of type [unit -> string] to benchmark. *)
  label : string option;
      (** Optional display name. The qualified definition name is used when
          omitted. *)
}

(** One compilation configuration applied to every benchmark subject. *)
type configuration = {
  backend : backend;  (** Extraction and native compilation backend. *)
  flags : string;
      (** User-supplied compiler arguments, parsed without invoking a shell. *)
}

(** [run ~opaque_access subjects configurations] validates [subjects], creates
    and compiles every subject/configuration pair, checks that all executables
    produce identical stdout, and reports the Hyperfine comparison.

    Invalid requests, unavailable tools, failed compilation or execution, and
    observationally different output are reported as Rocq user errors.

    @param opaque_access accessor used when Crane extracts opaque definitions *)
val run :
  opaque_access:Global.indirect_accessor ->
  subject list ->
  configuration list ->
  unit
