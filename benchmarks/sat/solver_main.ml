(* OCaml side: hand the bytes of a DIMACS file to the extracted solver's
   tree, run it through the interpreter, report. *)
module R = Itree_run.Make (Solver_ml)

let () =
  let bytes = Solver_main_common.read_bytes Sys.argv.(1) in
  let big = 1 lsl 61 in
  (* At most one conflict per step: code + 8 * conflicts stays below max_int. *)
  let budget = 1 lsl 58 in
  let t0 = Unix.gettimeofday () in
  let r =
    try R.run (Obj.magic (Solver_ml.Solver.solve_dimacs big budget bytes))
    with Vec_impl.Out_of_fuel _ -> 2 in
  Solver_main_common.report r (Unix.gettimeofday () -. t0)
