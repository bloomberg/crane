(** Crane extraction of [SolverGlobal]: the solver on [Global] arrays. *)
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.Error.
Require Import SolverGlobal.
Set Crane Loopify.
Set Crane SharedVariant.
Crane Extraction "solver_global" SolverGlobal.
