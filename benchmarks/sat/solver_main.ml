(* OCaml side: hand the bytes of a DIMACS file to the extracted solver,
   which parses and solves them, and report, as solver_main.cpp does. *)
let () =
  let ic = open_in_bin Sys.argv.(1) in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let bytes = Array.init (String.length s) (fun i -> Char.code s.[i]) in
  let big = 1 lsl 61 in
  (* At most one conflict per step: code + 8 * conflicts stays below max_int. *)
  let budget = 1 lsl 58 in
  let t0 = Unix.gettimeofday () in
  let r =
    try Solver_ml.Solver.solve_dimacs big budget bytes (Array.length bytes)
    with Sat_rt.Out_of_fuel -> 2 in
  let secs = Unix.gettimeofday () -. t0 in
  let names = [| "UNSAT"; "SAT"; "UNKNOWN"; "BADMODEL"; "INVALID"; "?"; "?"; "?" |] in
  Printf.printf "%s conflicts=%d time=%.4f\n" names.(r mod 8) (r / 8) secs
