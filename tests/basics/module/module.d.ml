(* Differential test harness: prints canonical output for diffing against C++ *)
let print_find key map =
  match Module_ocaml.NatMap.find key map with
  | Some v -> Printf.printf "find(%d)=%d\n" key v
  | None -> Printf.printf "find(%d)=None\n" key

let () =
  print_find 1 Module_ocaml.mymap;
  print_find 2 Module_ocaml.mymap;
  print_find 3 Module_ocaml.mymap;
  print_find 4 Module_ocaml.mymap
