(* Driver for the hand-erased control: the solver's result is direct. *)
let () =
  let nvars, input = Solver_main_common.read_dimacs Sys.argv.(1) in
  let big = 1 lsl 61 in
  (* At most one conflict per step: code + 8 * conflicts stays below max_int. *)
  let budget = 1 lsl 58 in
  let t0 = Unix.gettimeofday () in
  let r =
    try Solver_direct_ml.Solver.solve big budget nvars input (Vec_impl.len input)
    with Vec_impl.Out_of_fuel _ -> 2 in
  Solver_main_common.report r (Unix.gettimeofday () -. t0)
