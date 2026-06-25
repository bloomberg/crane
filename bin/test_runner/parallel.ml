(** Two-phase parallel test execution.

    {2 Phase 1: Build}

    All test executables are compiled in a single [dune build] invocation,
    which lets dune's own scheduler maximise parallelism across Rocq
    extraction, C++ compilation, and linking.  Tests that fail to compile
    are detected by checking whether their [.t.exe] exists afterwards.

    {2 Phase 2: Run}

    Successfully compiled executables are distributed across [N] forked
    worker processes.  Each worker runs its assigned tests sequentially
    and writes results to a temporary file using {!Marshal}.  The parent
    collects all result files after all workers exit.

    {2 Load balancing}

    A naive round-robin partition leads to poor utilisation when a few
    tests dominate runtime (e.g. concurrent STM hash map stress tests at
    ~17 s each).  Instead, we use a {b greedy longest-first} strategy:
    tests are sorted by estimated duration (longest first), then each
    test is assigned to the worker with the smallest accumulated load.
    Estimates come from a {b timing cache} that records wall-clock
    durations from previous runs.

    {2 Timing cache}

    Stored at [_build/.crane_test_times] (one line per test:
    ["category/name duration\n"]).  Lives inside [_build/] so that
    [dune clean] removes it.  The cache only affects scheduling order —
    it has no effect on which tests run or their pass/fail status.
    When saving, stale entries (tests that no longer exist on disk) are
    pruned by intersecting with the current test set. *)

open Types

(** [run_executable test_dir exe_name] forks a child that execs the test
    binary at [test_dir/exe_name], capturing stdout+stderr via a pipe.
    Returns [(passed, output, duration_seconds)].  The child's working
    directory is set to [test_dir] so that tests can access sibling files. *)
let run_executable test_dir exe_name =
  let exe_path = Filename.concat test_dir exe_name in
  let start_time = Unix.gettimeofday () in
  let read_fd, write_fd = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then (
    Unix.close read_fd;
    Unix.dup2 write_fd Unix.stdout;
    Unix.dup2 write_fd Unix.stderr;
    Unix.close write_fd;
    Unix.chdir test_dir;
    try Unix.execv exe_path [|exe_path|] with _ -> exit 127 )
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
    let end_time = Unix.gettimeofday () in
    let passed =
      match status with
      | Unix.WEXITED 0 -> true
      | _ -> false
    in
    (passed, Buffer.contents buffer, end_time -. start_time) )

(** [build_batch targets] runs [dune build <targets>] in a forked child
    with stdout/stderr suppressed.  Returns [true] on exit code 0.
    Dune continues past individual target failures by default, so a
    [false] return typically means a dune-level error (not a single test
    failing to compile). *)
let build_batch targets =
  let args = "build" :: targets in
  let pid = Unix.fork () in
  if pid = 0 then (
    let dev_null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
    Unix.dup2 dev_null Unix.stdout;
    Unix.dup2 dev_null Unix.stderr;
    Unix.close dev_null;
    try Unix.execvp "dune" (Array.of_list ("dune" :: args)) with _ -> exit 127 )
  else
    let _, status = Unix.waitpid [] pid in
    match status with
    | Unix.WEXITED 0 -> true
    | _ -> false

(** [build_all_tests config tests] compiles every test executable in a
    single [dune build] call.  Returns the list of tests whose [.t.exe]
    was not produced (i.e. compilation failures). *)
let build_all_tests config tests =
  let target_of t =
    Printf.sprintf "tests/%s/%s/%s.t.exe" t.category t.name t.name
  in
  let targets = List.map target_of tests in
  if targets <> [] then ignore (build_batch targets);
  let exe_path_of t =
    Printf.sprintf "%s/_build/default/tests/%s/%s/%s.t.exe" config.project_root
      t.category t.name t.name
  in
  List.filter (fun t -> not (Sys.file_exists (exe_path_of t))) tests

(** [run_test config test] executes a single already-compiled test binary
    from [_build/default/tests/<category>/<name>/]. *)
let run_test config test =
  let test_dir =
    Printf.sprintf
      "%s/_build/default/tests/%s/%s"
      config.project_root
      test.category
      test.name
  in
  let exe_name = Printf.sprintf "./%s.t.exe" test.name in
  let passed, output, duration = run_executable test_dir exe_name in
  {test; passed; output; duration}

(** [run_tests_batch config tests output_file] runs [tests] sequentially
    and serialises the results to [output_file] using {!Marshal}.
    Called inside each forked worker process. *)
let run_tests_batch config tests output_file =
  let results = List.map (run_test config) tests in
  let oc = open_out_bin output_file in
  Marshal.to_channel oc results [];
  close_out oc

(** [read_results_file file] deserialises the {!test_result} list
    written by {!run_tests_batch}. *)
let read_results_file file =
  let ic = open_in_bin file in
  let results : test_result list = Marshal.from_channel ic in
  close_in ic;
  results

(** {2 Timing cache} *)

(** Path to the timing cache file: [<root>/_build/.crane_test_times]. *)
let timing_cache_path root =
  Filename.concat root (Filename.concat "_build" ".crane_test_times")

(** [load_timing_cache root] reads the timing cache into a hash table
    mapping ["category/name"] to duration in seconds.  Returns an empty
    table if the file does not exist or cannot be parsed. *)
let load_timing_cache root =
  let path = timing_cache_path root in
  let tbl = Hashtbl.create 128 in
  ( try
      let ic = open_in path in
      ( try
          while true do
            let line = input_line ic in
            match String.index_opt line ' ' with
            | Some i ->
              let key = String.sub line 0 i in
              let dur = float_of_string (String.sub line (i + 1) (String.length line - i - 1)) in
              Hashtbl.replace tbl key dur
            | None -> ()
          done
        with End_of_file -> () );
      close_in ic
    with Sys_error _ -> () );
  tbl

(** [save_timing_cache root results all_tests] merges [results] into the
    existing cache and writes it back, pruning any entries whose key does
    not appear in [all_tests].  This prevents stale entries from
    accumulating when tests are renamed or deleted. *)
let save_timing_cache root results all_tests =
  let path = timing_cache_path root in
  let valid_keys = Hashtbl.create (List.length all_tests) in
  List.iter (fun t ->
    Hashtbl.replace valid_keys (t.category ^ "/" ^ t.name) true
  ) all_tests;
  let existing = load_timing_cache root in
  List.iter
    (fun (r : test_result) ->
      let key = r.test.category ^ "/" ^ r.test.name in
      Hashtbl.replace existing key r.duration)
    results;
  ( try
      let oc = open_out path in
      Hashtbl.iter (fun k v ->
        if Hashtbl.mem valid_keys k then
          Printf.fprintf oc "%s %.3f\n" k v
      ) existing;
      close_out oc
    with Sys_error _ -> () )

(** {2 Load-balanced partitioning} *)

(** [partition_greedy n tests timing_cache] distributes [tests] across
    [n] buckets using greedy longest-first scheduling.

    Tests are sorted by estimated duration (descending), then each test
    is assigned to the bucket with the smallest total load so far.
    Tests not found in [timing_cache] are assumed to take 0.1 s.

    This is a 2-approximation to optimal makespan scheduling (LPT rule)
    and works well in practice because a handful of tests (STM hash maps,
    deep trees) dominate the runtime while the remaining ~590 tests each
    take <100 ms. *)
let partition_greedy n lst timing_cache =
  let estimated t =
    let key = t.category ^ "/" ^ t.name in
    match Hashtbl.find_opt timing_cache key with
    | Some d -> d
    | None -> 0.1
  in
  let sorted = List.sort (fun a b ->
    compare (estimated b) (estimated a)) lst in
  let loads = Array.make n 0.0 in
  let buckets = Array.make n [] in
  List.iter (fun t ->
    let min_i = ref 0 in
    for i = 1 to n - 1 do
      if loads.(i) < loads.(!min_i) then min_i := i
    done;
    buckets.(!min_i) <- t :: buckets.(!min_i);
    loads.(!min_i) <- loads.(!min_i) +. estimated t
  ) sorted;
  Array.map List.rev buckets

(** {2 Top-level entry point} *)

(** [run_tests_parallel config tests] builds and runs all [tests],
    returning a list of {!test_result} sorted by {!compare_test_id}.

    Phase 1 compiles every test in one [dune build] call.  Phase 2
    distributes runnable executables across [config.jobs] forked workers
    using {!partition_greedy} for load balancing.  Each worker writes its
    results to a temp file; the parent collects and merges them.

    Tests that fail to compile are included in the results with
    [passed = false] and [output = "Compilation failed"]. *)
let run_tests_parallel config tests =
  if tests = [] then
    []
  else
    (* Phase 1: Build all tests in one dune call *)
    let compile_failures = build_all_tests config tests in
    let compile_fail_set = Hashtbl.create 16 in
    List.iter
      (fun t -> Hashtbl.replace compile_fail_set (t.category ^ "/" ^ t.name) true)
      compile_failures;
    let runnable =
      List.filter
        (fun t -> not (Hashtbl.mem compile_fail_set (t.category ^ "/" ^ t.name)))
        tests
    in
    let compile_fail_results =
      List.map
        (fun t ->
          { test = t;
            passed = false;
            output = "Compilation failed";
            duration = 0.0
          })
        compile_failures
    in

    (* Phase 2: Run test executables in parallel *)
    let num_workers = min config.jobs (List.length runnable) in
    let batches = partition_greedy num_workers runnable (load_timing_cache config.project_root) in
    let tmpdir = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in

    let workers =
      Array.mapi
        (fun i batch ->
          if batch = [] then
            None
          else
            let output_file =
              Printf.sprintf "%s/crane_test_%d_%d" tmpdir (Unix.getpid ()) i
            in
            let pid = Unix.fork () in
            if pid = 0 then (
              run_tests_batch config batch output_file;
              exit 0 )
            else
              Some (pid, output_file) )
        batches
    in

    let all_results =
      Array.fold_left
        (fun acc worker ->
          match worker with
          | None -> acc
          | Some (pid, output_file) ->
            let _, status = Unix.waitpid [] pid in
            let results =
              if status = Unix.WEXITED 0 && Sys.file_exists output_file then (
                let r = read_results_file output_file in
                Sys.remove output_file;
                r )
              else
                []
            in
            results @ acc )
        []
        workers
    in

    List.sort (fun a b -> compare_test_id a.test b.test)
      (compile_fail_results @ all_results)
