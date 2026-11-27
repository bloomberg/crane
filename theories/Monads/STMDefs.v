(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared STM effect definitions (flavor-independent).

   Contains the effect inductives ([tvarE], [stmVecE], [stmControlE]),
   composed effect ([stmE]), axioms, and smart constructors that are
   identical across library flavors. Flavor files ([STM.v], [STMBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs External.VectorDefs.

Open Scope itree_scope.

Axiom TVar : Type -> Type.

Inductive tvarE : Type -> Type :=
| NewTVar : forall {A}, A -> tvarE (TVar A)
| ReadTVar : forall {A}, TVar A -> tvarE A
| WriteTVar : forall {A}, TVar A -> A -> tvarE unit.

Inductive stmVecE : Type -> Type :=
| GetSTM : forall {A}, vector A -> int -> stmVecE A
| IsEmptySTM : forall {A}, vector A -> stmVecE bool.

Inductive stmControlE : Type -> Type :=
| Retry : forall A, stmControlE A.

Crane Extract Inductive stmVecE => ""
  [ "%a0.at(%a1)" "%a0.empty()" ].
Crane Extract Inductive stmControlE => ""
  [ "stm::retry<%t0>()" ].

Definition stmE := tvarE +' stmVecE +' stmControlE.
Crane Extract Skip stmE.

Axiom atomically : forall {E} `{ioE -< E} {A}, itree stmE A -> itree E A.
Axiom or_else : forall {A}, itree stmE A -> itree stmE A -> itree stmE A.

Definition new_tvar {E} `{tvarE -< E} {A} (a : A) : itree E (TVar A) := embed (NewTVar a).
Definition read_tvar {E} `{tvarE -< E} {A} (v : TVar A) : itree E A := embed (ReadTVar v).
Definition write_tvar {E} `{tvarE -< E} {A} (v : TVar A) (a : A) : itree E unit := embed (WriteTVar v a).

Definition retry {A} : itree stmE A := embed (Retry A).

Definition get_stm {E} `{stmVecE -< E} {A} (v : vector A) (i : int) : itree E A := embed (GetSTM v i).
Definition is_empty_stm {E} `{stmVecE -< E} {A} (v : vector A) : itree E bool := embed (IsEmptySTM v).

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant or_else => "stm::orElse<%t0>(%a0, %a1)".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
(* At the TVar's element type, which a lambda's own closure type is not. *)
Crane Extract Inlined Constant new_tvar => "stm::newTVar<%t1>(%a0)".
Crane Extract Inlined Constant get_stm => "%a0.at(%a1)".
Crane Extract Inlined Constant is_empty_stm => "%a0.empty()".

Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

Definition modify_tvar {A : Type} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- read_tvar a ;;
  write_tvar a (f val) ;;
  Ret tt.
