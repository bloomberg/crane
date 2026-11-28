(** Crane extraction of [Solver] on [vecE].  Loopify turns every fuel loop
    into a [while] loop: without it the by-value [shared_ptr] arguments
    block tail calls and the C++ overflows the stack. *)
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree.
Require Import CraneVec Solver.
Set Crane Loopify.
Set Crane SharedVariant.
Crane Extraction "solver" Solver.
