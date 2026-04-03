(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrency effects using [std::thread].

   Provides thread effects ([concE]) as composable inductives with smart
   constructors and C++ extraction mappings. Use [itree concE A] (or any
   composed effect containing [threadE]) as the monadic type.

   Console output ([print_endline]) is reused from [IO.v] via [consoleE].

   [mk_thread] remains an axiom because its higher-order argument [(A -> B)]
   cannot satisfy universe constraints when [B] is an [itree] type.
*)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Open Scope itree_scope.

Axiom thread : Type.

Inductive threadE : Type -> Type :=
| Join : thread -> threadE unit
| Sleep : int -> threadE unit.

Crane Extract Skip threadE.

Definition concE := threadE +' consoleE.
Crane Extract Skip concE.

Axiom mk_thread : forall {E} `{threadE -< E} {A B},
  (A -> B) -> A -> itree E thread.
Definition join {E} `{threadE -< E} (t : thread) : itree E unit :=
  embed (Join t).
Definition sleep {E} `{threadE -< E} (d : int) : itree E unit :=
  embed (Sleep d).

Crane Extract Inlined Constant thread => "std::thread" From "thread".
Crane Extract Inlined Constant mk_thread => "std::thread(%a0, %a1)".
Crane Extract Inlined Constant join => "%a0.join()".
Crane Extract Inlined Constant sleep =>
  "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))"
  From "thread" "chrono".

Axiom runConc : forall {A}, itree concE A -> A.
Crane Extract Inlined Constant runConc => "%a0".
