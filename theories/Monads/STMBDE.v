(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events (BDE flavor).

   Provides STM effects ([stmE]) as composable inductives with smart constructors
   and C++ extraction mappings. Use [itree stmE A] as the monadic type.

   Smart constructors are polymorphic over the effect type [E] via [-<],
   so they can be used in any composed effect that includes the relevant
   sub-effect.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.ITree Monads.IOBDE External.VectorBDE.

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

Crane Extract Skip tvarE.
Crane Extract Skip stmVecE.
Crane Extract Skip stmControlE.

Definition stmE := tvarE +' stmVecE +' stmControlE.
Crane Extract Skip stmE.

Axiom atomically : forall {A}, itree stmE A -> itree ioE A.
Axiom orElse : forall {A}, itree stmE A -> itree stmE A -> itree stmE A.

Definition newTVar {E} `{tvarE -< E} {A} (a : A) : itree E (TVar A) := embed (NewTVar a).
Definition readTVar {E} `{tvarE -< E} {A} (v : TVar A) : itree E A := embed (ReadTVar v).
Definition writeTVar {E} `{tvarE -< E} {A} (v : TVar A) (a : A) : itree E unit := embed (WriteTVar v a).

Definition retry {A} : itree stmE A := embed (Retry A).

Definition getSTM {E} `{stmVecE -< E} {A} (v : vector A) (i : int) : itree E A := embed (GetSTM v i).
Definition isEmptySTM {E} `{stmVecE -< E} {A} (v : vector A) : itree E bool := embed (IsEmptySTM v).

Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

Definition modifyTVar {A : Type} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.

Crane Extract Inlined Constant TVar => "bsl::shared_ptr<stm::TVar<%t0>>" From "mini_stm.h".

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".

Crane Extract Inlined Constant newTVar => "stm::newTVar(%a0)".
Crane Extract Inlined Constant readTVar => "stm::readTVar(%a0)".
Crane Extract Inlined Constant writeTVar => "stm::writeTVar(%a0, %a1)".

Crane Extract Inlined Constant getSTM => "%a0.at(%a1)".
Crane Extract Inlined Constant isEmptySTM => "%a0.empty()".
