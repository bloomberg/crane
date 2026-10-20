From Stdlib Require Import Extraction.
Require Import OcamlNat SatVec Solver.
Extract Constant vec "'a" => "'a Vec_impl.t".
Extraction "solver_ml.ml" Solver.solve.
