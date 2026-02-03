open Types

let get_cpu_count () =
  try
    if Sys.os_type = "Unix" then
      let ic = Unix.open_process_in "sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4" in
      let line = input_line ic in
      ignore (Unix.close_process_in ic);
      int_of_string (String.trim line)
    else 4
  with _ -> 4

let parse_args () =
  let jobs = ref (get_cpu_count ()) in
  let verbose = ref false in
  let specs = [
    ("-j", Arg.Set_int jobs, "N Number of parallel jobs (default: CPU count)");
    ("--jobs", Arg.Set_int jobs, "N Number of parallel jobs (default: CPU count)");
    ("-v", Arg.Set verbose, " Verbose output (show error details)");
    ("--verbose", Arg.Set verbose, " Verbose output (show error details)");
  ] in
  let usage = "Usage: crane-test-runner [options]" in
  Arg.parse specs (fun _ -> ()) usage;
  let project_root = Sys.getcwd () in
  { jobs = !jobs; verbose = !verbose; project_root }

let main () =
  let config = parse_args () in
  let tests = Discovery.find_all_tests config.project_root in

  if tests = [] then begin
    Printf.eprintf "No tests found\n";
    exit 0
  end;

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
