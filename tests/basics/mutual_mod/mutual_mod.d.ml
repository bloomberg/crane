(* Differential test harness: prints canonical output for diffing against C++ *)
let () =
  Printf.printf "test_even_len=%d\n" Mutual_mod_ocaml.test_even_len;
  Printf.printf "test_odd_len=%d\n" Mutual_mod_ocaml.test_odd_len
