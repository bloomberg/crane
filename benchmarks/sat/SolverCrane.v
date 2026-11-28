(** Crane extraction of [Solver].  Global arrays become
    [crane::array_storage] handles and every access a direct index; Loopify
    turns every loop into a [while] loop, so the C++ runs in constant
    stack. *)
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.Error.
Require Import Solver.
Set Crane Loopify.
Set Crane SharedVariant.
Crane Extraction "solver" Solver.
