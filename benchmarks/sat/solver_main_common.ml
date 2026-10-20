(* DIMACS reading and result printing, shared by the OCaml drivers. *)
let read_dimacs path =
  let ic = open_in path in
  let nvars = ref 0 and flat = Vec_impl.make 0 0 and cl = ref [] in
  (try
     while true do
       let line = String.trim (input_line ic) in
       if line = "" || line.[0] = 'c' || line.[0] = '%' then ()
       else if line.[0] = 'p' then
         Scanf.sscanf line "p cnf %d %d" (fun nv _ -> nvars := nv)
       else
         String.split_on_char ' ' line
         |> List.filter (( <> ) "")
         |> List.iter (fun tok ->
                let x = int_of_string tok in
                if x = 0 then begin
                  let lits = List.rev !cl in
                  Vec_impl.push flat (List.length lits);
                  List.iter (Vec_impl.push flat) lits;
                  cl := []
                end
                else cl := ((2 * (abs x - 1)) + if x < 0 then 1 else 0) :: !cl)
     done
   with End_of_file -> ());
  close_in ic;
  (!nvars, flat)

let report r secs =
  let names = [| "UNSAT"; "SAT"; "UNKNOWN"; "BADMODEL"; "INVALID"; "?"; "?"; "?" |] in
  Printf.printf "%s conflicts=%d time=%.4f\n" names.(r mod 8) (r / 8) secs
