(** Entry point for the Crane test runner.

    Discovers all tests under [tests/], optionally filters by category
    or changed-file status, then delegates to {!Parallel.run_tests_parallel}
    for a two-phase build-then-run execution.  After the run, the timing
    cache is updated for future load balancing.

    {2 Usage}

    {v
    crane-test-runner [options]

      -j, --jobs N      Number of parallel workers (default: CPU count)
      -v, --verbose     Print stdout/stderr for failed tests
      --folder NAME     Restrict to one category (basics, monadic, regression, wip)
      --changed         Only run tests whose files differ from HEAD
    v}

    Typical invocation via Make:
    - [make test]         — extract all .vo files, then build and run all tests
    - [make test-one TEST=list] — build and run a single test *)

open Types

(** Detect the number of logical CPUs.  Falls back to 4 on failure. *)
let get_cpu_count () =
  try
    if Sys.os_type = "Unix" then (
      let ic =
        Unix.open_process_in
          "sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4"
      in
      let line = input_line ic in
      ignore (Unix.close_process_in ic);
      int_of_string (String.trim line) )
    else
      4
  with _ -> 4

(** Parse command-line arguments into a {!config}. *)
let parse_args () =
  let jobs = ref (get_cpu_count ()) in
  let verbose = ref false in
  let folder = ref None in
  let changed_only = ref false in
  let specs =
    [
      ("-j", Arg.Set_int jobs, "N Number of parallel jobs (default: CPU count)");
      ( "--jobs",
        Arg.Set_int jobs,
        "N Number of parallel jobs (default: CPU count)" );
      ("-v", Arg.Set verbose, " Verbose output (show error details)");
      ("--verbose", Arg.Set verbose, " Verbose output (show error details)");
      ( "--folder",
        Arg.String (fun f -> folder := Some f),
        " Run tests only from specified folder (basics, monadic, wip, \
         regression)" );
      ("--changed", Arg.Set changed_only, " Only compile/run tests with changed files");
    ]
  in
  let usage = "Usage: crane-test-runner [options]" in
  Arg.parse specs (fun _ -> ()) usage;
  let project_root = Sys.getcwd () in
  {jobs = !jobs; verbose = !verbose; project_root; folder = !folder;
   changed_only = !changed_only}

let main () =
  let config = parse_args () in
  let all_tests = Discovery.find_all_tests config.project_root in

  (* Apply optional filters: --folder and --changed *)
  let tests =
    match config.folder with
    | None -> all_tests
    | Some folder -> List.filter (fun t -> t.category = folder) all_tests
  in

  let tests =
    if config.changed_only then
      let changed = Discovery.find_changed_tests config.project_root in
      let changed_set = Hashtbl.create 32 in
      List.iter (fun t -> Hashtbl.replace changed_set (t.category ^ "/" ^ t.name) true) changed;
      let filtered = List.filter (fun t -> Hashtbl.mem changed_set (t.category ^ "/" ^ t.name)) tests in
      Printf.printf "Changed tests: %d / %d\n" (List.length filtered) (List.length tests);
      filtered
    else
      tests
  in

  ( if tests = [] then (
      ( match config.folder with
      | None ->
        if config.changed_only then
          Printf.printf "No changed tests to run\n"
        else
          Printf.eprintf "No tests found\n"
      | Some folder ->
        Printf.eprintf "No tests found in folder '%s'\n" folder );
      exit 0 ) );

  Output.print_header ();

  let t0 = Unix.gettimeofday () in
  let results = Parallel.run_tests_parallel config tests in
  let elapsed = Unix.gettimeofday () -. t0 in

  (* Update the timing cache with results from this run.  [all_tests] is
     passed so that entries for deleted/renamed tests can be pruned. *)
  Parallel.save_timing_cache config.project_root results all_tests;

  Output.print_results results;
  Output.print_summary results elapsed;

  if config.verbose then
    Output.print_verbose_errors results 40;

  let failed = List.exists (fun r -> not r.passed) results in
  exit (if failed then 1 else 0)

let () =
  try main ()
  with e ->
    Printf.eprintf "Error: %s\n" (Printexc.to_string e);
    exit 2
