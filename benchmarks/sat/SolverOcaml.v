From Stdlib Require Import Extraction.
Require Import OcamlNat SatVec Solver.
Extract Inductive vec => "Vec_impl.t" [ "(fun _ -> assert false)" ].
Extraction "solver_ml.ml" Solver.solve Solver.solve_dimacs.
