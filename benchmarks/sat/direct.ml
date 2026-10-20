(* The erased tree for [SolverOcamlDirect]: a computation is its result. *)
type ('e, 'r) t = 'r
let go _ = assert false
let observe _ = assert false
