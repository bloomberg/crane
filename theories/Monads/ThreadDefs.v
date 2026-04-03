(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared thread effect definitions (flavor-independent).

   Contains the [thread] axiom, the [threadE] effect inductive, the
   composed effect [concE], and smart constructors that are identical
   across library flavors. Flavor files ([Thread.v], [ThreadBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.

   [spawn] remains an axiom because its higher-order argument [(A -> B)]
   cannot satisfy universe constraints when [B] is an [itree] type.
*)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs.

Axiom thread : Type.

Inductive threadE : Type -> Type :=
| Join : thread -> threadE unit
| Sleep : int -> threadE unit.

Definition concE := threadE +' consoleE.
Crane Extract Skip concE.

Axiom spawn : forall {E} `{threadE -< E} {A B},
  (A -> B) -> A -> itree E thread.
Definition join {E} `{threadE -< E} (t : thread) : itree E unit :=
  embed (Join t).
Definition sleep {E} `{threadE -< E} (d : int) : itree E unit :=
  embed (Sleep d).

Crane Extract Inlined Constant join => "%a0.join()".

Axiom runConc : forall {A}, itree concE A -> A.
Crane Extract Inlined Constant runConc => "%a0".
