(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared clock effect definitions (flavor-independent).

   Contains the effect inductive ([clockE]) and smart constructors that are
   identical across library flavors. Flavor files ([Clock.v], [ClockBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.

   All timestamps are returned as [int] (int63) representing milliseconds.
   [now] is an alias for [system_now] (wall-clock time).
*)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

Inductive clockE : Type -> Type :=
| SteadyNow : clockE int
| SystemNow : clockE int.

Definition steady_now {E} `{clockE -< E} : itree E int := embed SteadyNow.
Definition system_now {E} `{clockE -< E} : itree E int := embed SystemNow.
Definition now {E} `{clockE -< E} : itree E int := system_now.
