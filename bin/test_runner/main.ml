open Types

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

  let results = Parallel.run_tests_parallel config tests in

  Output.print_results results;
  Output.print_summary results;

  if config.verbose then
    Output.print_verbose_errors results 40;

  let failed = List.exists (fun r -> not r.passed) results in
  exit (if failed then 1 else 0)

let () =
  try main ()
  with e ->
    Printf.eprintf "Error: %s\n" (Printexc.to_string e);
    exit 2
