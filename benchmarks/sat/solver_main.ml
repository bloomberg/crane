(* OCaml side: read a DIMACS file, run the extracted solver's tree through
   the interpreter, report. *)
module R = Itree_run.Make (Solver_ml)

let () =
  let nvars, input = Solver_main_common.read_dimacs Sys.argv.(1) in
  let big = 1 lsl 61 in
  (* At most one conflict per step: code + 8 * conflicts stays below max_int. *)
  let budget = 1 lsl 58 in
  let t0 = Unix.gettimeofday () in
  let r =
    try R.run (Obj.magic (Solver_ml.Solver.solve big budget nvars input (Vec_impl.len input)))
    with Vec_impl.Out_of_fuel _ -> 2 in
  Solver_main_common.report r (Unix.gettimeofday () -. t0)
