open Types

let run_command cmd args =
  let read_fd, write_fd = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then begin
    Unix.close read_fd;
    Unix.dup2 write_fd Unix.stdout;
    Unix.dup2 write_fd Unix.stderr;
    Unix.close write_fd;
    try
      Unix.execvp cmd (Array.of_list (cmd :: args))
    with _ ->
      exit 127
  end else begin
    Unix.close write_fd;
    let buffer = Buffer.create 4096 in
    let bytes = Bytes.create 4096 in
    let rec read_all () =
      let n = Unix.read read_fd bytes 0 4096 in
      if n > 0 then begin
        Buffer.add_subbytes buffer bytes 0 n;
        read_all ()
      end
    in
    read_all ();
    Unix.close read_fd;
    let _, status = Unix.waitpid [] pid in
    let exit_code = match status with
      | Unix.WEXITED code -> code
      | Unix.WSIGNALED _ -> 128
      | Unix.WSTOPPED _ -> 128
    in
    (exit_code, Buffer.contents buffer)
  end

let run_test _config test =
  let target = test_to_dune_target test in
  let start_time = Unix.gettimeofday () in
  let exit_code, output = run_command "dune" ["build"; target] in
  let end_time = Unix.gettimeofday () in
  {
    test;
    passed = (exit_code = 0);
    output;
    duration = end_time -. start_time;
  }
