(* Driver for the hand-erased control: the solver's result is direct. *)
let () =
  let nvars, input = Solver_main_common.read_dimacs Sys.argv.(1) in
  let big = 1 lsl 61 in
  let t0 = Unix.gettimeofday () in
  let r = Solver_direct_ml.Solver.solve big big nvars input (Vec_impl.len input) in
  Solver_main_common.report r (Unix.gettimeofday () -. t0)
