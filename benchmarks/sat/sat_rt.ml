(* What the OCaml extraction of the solver (SolverOcaml.v) runs on: the
   erased tree and Global arrays as OCaml arrays.  The other Global
   operations are inlined there; accesses are unchecked under -unsafe, as
   in the C++. *)

(* A loop ran out of fuel (Solver.out_of_fuel). *)
exception Out_of_fuel

(* An erased computation is its result; nothing builds or inspects a node. *)
type ('e, 'r) t = 'r
let go _ = assert false
let observe _ = assert false

(* A Global array over locations ['t] of ['a]s. *)
type ('t, 'a) array = 'a Stdlib.Array.t

(* Exchange two elements of [a]. *)
let swap a i j =
  let x = Stdlib.Array.unsafe_get a i in
  Stdlib.Array.unsafe_set a i (Stdlib.Array.unsafe_get a j);
  Stdlib.Array.unsafe_set a j x
