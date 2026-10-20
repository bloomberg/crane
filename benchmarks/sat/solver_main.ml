(* OCaml side: read a DIMACS file, run the extracted solver's tree through
   the interpreter, report. *)
module R = Itree_run.Make (Solver_ml)

let () =
  let nvars, input = Solver_main_common.read_dimacs Sys.argv.(1) in
  let big = 1 lsl 61 in
  let t0 = Unix.gettimeofday () in
  let r = R.run (Obj.magic (Solver_ml.Solver.solve big big nvars input (Vec_impl.len input))) in
  Solver_main_common.report r (Unix.gettimeofday () -. t0)
