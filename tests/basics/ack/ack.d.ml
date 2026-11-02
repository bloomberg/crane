(* Differential test harness: prints canonical output for diffing against C++ *)
let () =
  Printf.printf "ack(0,0)=%d\n" (Ack_ocaml.Ack.ack 0 0);
  Printf.printf "ack(0,1)=%d\n" (Ack_ocaml.Ack.ack 0 1);
  Printf.printf "ack(0,5)=%d\n" (Ack_ocaml.Ack.ack 0 5);
  Printf.printf "ack(1,0)=%d\n" (Ack_ocaml.Ack.ack 1 0);
  Printf.printf "ack(1,1)=%d\n" (Ack_ocaml.Ack.ack 1 1);
  Printf.printf "ack(1,5)=%d\n" (Ack_ocaml.Ack.ack 1 5);
  Printf.printf "ack(2,0)=%d\n" (Ack_ocaml.Ack.ack 2 0);
  Printf.printf "ack(2,1)=%d\n" (Ack_ocaml.Ack.ack 2 1);
  Printf.printf "ack(2,2)=%d\n" (Ack_ocaml.Ack.ack 2 2);
  Printf.printf "ack(2,4)=%d\n" (Ack_ocaml.Ack.ack 2 4);
  Printf.printf "ack(3,0)=%d\n" (Ack_ocaml.Ack.ack 3 0);
  Printf.printf "ack(3,1)=%d\n" (Ack_ocaml.Ack.ack 3 1);
  Printf.printf "ack(3,2)=%d\n" (Ack_ocaml.Ack.ack 3 2);
  Printf.printf "ack(3,3)=%d\n" (Ack_ocaml.Ack.ack 3 3);
  Printf.printf "ack(3,7)=%d\n" (Ack_ocaml.Ack.ack 3 7)
