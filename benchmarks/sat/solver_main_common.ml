(* File reading and result printing, shared by the OCaml drivers.  Parsing
   happens in Rocq (Solver.solve_dimacs); this only hands over the bytes. *)
let read_bytes path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let bytes = Vec_impl.make 0 0 in
  String.iter (fun c -> Vec_impl.push bytes (Char.code c)) s;
  bytes

let report r secs =
  let names = [| "UNSAT"; "SAT"; "UNKNOWN"; "BADMODEL"; "INVALID"; "?"; "?"; "?" |] in
  Printf.printf "%s conflicts=%d time=%.4f\n" names.(r mod 8) (r / 8) secs
