(** Single-test executor using [dune build].

    This module provides a simple one-at-a-time executor that invokes
    [dune build @tests/<category>/<name>/runtest] for each test.  It is
    used by the legacy sequential runner ({!run_test}) but is {b not} used
    by the parallel runner in {!Parallel}, which builds all executables in
    a single dune invocation and then runs them directly. *)

open Types

(** [run_command cmd args] forks a child that execs [cmd] with [args],
    capturing both stdout and stderr into a single string.
    Returns [(exit_code, captured_output)].  Signals map to exit code 128. *)
let run_command cmd args =
  let read_fd, write_fd = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then (
    Unix.close read_fd;
    Unix.dup2 write_fd Unix.stdout;
    Unix.dup2 write_fd Unix.stderr;
    Unix.close write_fd;
    try Unix.execvp cmd (Array.of_list (cmd :: args)) with _ -> exit 127 )
  else (
    Unix.close write_fd;
    let buffer = Buffer.create 4096 in
    let bytes = Bytes.create 4096 in
    let rec read_all () =
      let n = Unix.read read_fd bytes 0 4096 in
      if n > 0 then (
        Buffer.add_subbytes buffer bytes 0 n;
        read_all () )
    in
    read_all ();
    Unix.close read_fd;
    let _, status = Unix.waitpid [] pid in
    let exit_code =
      match status with
      | Unix.WEXITED code -> code
      | Unix.WSIGNALED _ -> 128
      | Unix.WSTOPPED _ -> 128
    in
    (exit_code, Buffer.contents buffer) )

(** [run_test _config test] builds and runs a single test via its dune
    [runtest] alias.  The returned {!test_result.duration} covers the
    entire dune invocation (extraction + C++ compilation + execution). *)
let run_test _config test =
  let target = test_to_dune_target test in
  let start_time = Unix.gettimeofday () in
  let exit_code, output = run_command "dune" ["build"; target] in
  let end_time = Unix.gettimeofday () in
  {test; passed = exit_code = 0; output; duration = end_time -. start_time}
