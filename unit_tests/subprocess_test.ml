(* A child's processor-time limit: what it charges, and what it does not. *)

open Crane_plugin

let check name cond =
  if not cond then (
    Printf.eprintf "subprocess: %s\n" name;
    exit 1 )

let () =
  let open Subprocess in
  check "BSD minutes" (parse_cpu_time "  1:02.50" = Some 62.5);
  check "procps hours" (parse_cpu_time "01:00:03\n" = Some 3603.);
  check "days" (parse_cpu_time "2-00:00:01" = Some 172801.);
  check "bare seconds" (parse_cpu_time "7" = Some 7.);
  check "empty" (parse_cpu_time "" = None);
  check "garbage" (parse_cpu_time "TIME" = None);
  check "too many fields" (parse_cpu_time "1:2:3:4" = None);
  (* The processor-time checks below need [ps] to read a child's time; a
     minimal container (no [procps]) has none, and without it [cpu_limit]
     falls back to wall time by design, which these checks don't expect. *)
  if executable_available "ps" then (
    (* A sleeping child uses no processor time: a limit shorter than its wall
       time does not stop it. *)
    check "sleep outlives a processor limit"
      (run ~cpu_limit:0.3 "sleep" ["1"] = Unix.WEXITED 0);
    (* A busy child is stopped once it has used its limit. *)
    check "busy child killed"
      (run ~stdout_file:"/dev/null" ~cpu_limit:0.3 ~timeout:600. "yes" []
       = Unix.WSIGNALED Sys.sigkill) )
  else Printf.eprintf "subprocess: no ps, skipping processor-time checks\n";
  (* The wall timeout still applies to a child using no processor time. *)
  check "wall timeout"
    (run ~cpu_limit:60. ~timeout:0.3 "sleep" ["5"] = Unix.WSIGNALED Sys.sigkill)
