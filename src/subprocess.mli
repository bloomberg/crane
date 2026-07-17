(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Shell-free subprocess execution helpers.

    Programs and arguments are passed directly to {!Unix.create_process}; none
    of the strings are interpreted by a command shell. This keeps compiler
    flags, temporary paths, and benchmark commands safe and predictable. *)

(** The complete observable result of a captured child process. *)
type captured_output = {
  status : Unix.process_status;  (** Termination status reported by [waitpid]. *)
  stdout : string;  (** Bytes written to standard output. *)
  stderr : string;  (** Bytes written to standard error. *)
}

(** [Invalid_arguments reason] indicates malformed text passed to
    {!split_arguments}. *)
exception Invalid_arguments of string

(** [executable_available executable] reports whether [executable] can be run
    from the current environment. Names without a directory separator are
    searched on [PATH]; explicit paths are checked directly. *)
val executable_available : string -> bool

(** [run ?stdout_file ?stderr_file program arguments] executes [program]
    directly and waits for it to terminate. Redirection files are truncated or
    created with permissions [0o600]. Unspecified streams remain inherited from
    the parent process.

    @return the child's raw {!Unix.process_status} *)
val run :
  ?stdout_file:string ->
  ?stderr_file:string ->
  string ->
  string list ->
  Unix.process_status

(** [capture program arguments] runs a child and captures stdout and stderr
    separately. Temporary capture files are removed even when execution raises.

    @return the child's status and captured streams *)
val capture : string -> string list -> captured_output

(** [exit_code status] converts [status] to a conventional integer exit code.
    Normal exits retain their code; signals and stopped states use [128 + n]. *)
val exit_code : Unix.process_status -> int

(** [split_arguments text] tokenizes a user-supplied argument string without
    invoking a shell. Whitespace separates tokens; single and double quotes
    group text; backslashes escape characters outside single quotes. Empty
    quoted strings are retained as empty arguments.

    @raise Invalid_arguments when a quote is unterminated or a final backslash
      has no character to escape *)
val split_arguments : string -> string list
