open Types

(* Two-phase parallel execution: Phase 1: Use single dune command to build all
   test executables (dune handles parallelism) Phase 2: Run test executables in
   parallel using fork *)

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

let build_all_tests config tests =
  (* Build all tests in a single dune invocation. Dune continues past
     failures by default (--stop-on-first-error is opt-in), so independent
     tests still compile even when others fail. We check which .t.exe files
     were produced afterwards. *)
  let target_of t =
    Printf.sprintf "tests/%s/%s/%s.t.exe" t.category t.name t.name
  in
  let targets = List.map target_of tests in
  if targets <> [] then ignore (build_batch targets);
  (* Return set of tests that failed to compile *)
  let exe_path_of t =
    Printf.sprintf "%s/_build/default/tests/%s/%s/%s.t.exe" config.project_root
      t.category t.name t.name
  in
  List.filter (fun t -> not (Sys.file_exists (exe_path_of t))) tests

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

let run_tests_batch config tests output_file =
  let results = List.map (run_test config) tests in
  let oc = open_out_bin output_file in
  Marshal.to_channel oc results [];
  close_out oc

let read_results_file file =
  let ic = open_in_bin file in
  let results : test_result list = Marshal.from_channel ic in
  close_in ic;
  results

let partition_list n lst =
  let arr = Array.make n [] in
  List.iteri (fun i x -> arr.(i mod n) <- x :: arr.(i mod n)) lst;
  Array.map List.rev arr

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
    let batches = partition_list num_workers runnable in
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
