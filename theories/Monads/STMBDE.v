(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.ITree Monads.IOBDE External.VectorBDE.

Import MonadNotations.

Module STM.

Module STM_axioms.
  Import IO_axioms.

  Axiom iSTM : Type -> Type.
  Axiom iatomically : forall {A}, iSTM A -> iIO A.
  Axiom iretry : forall {A}, iSTM A.
  Axiom iorElse : forall {A}, iSTM A -> iSTM A -> iSTM A.

  Axiom igetSTM : forall {A}, vector A -> int -> iSTM A.
  Axiom iisEmptySTM : forall {A}, vector A -> iSTM bool.

End STM_axioms.

Crane Extract Skip Module STM_axioms.
Import STM_axioms.

Definition STM : Type -> Type := itree iSTM.
Definition atomically {A} : STM A -> IO A := hoist (@iatomically).
Definition retry {A} : STM A := trigger (@iretry A).
(* Definition orElse {A} (l : STM A) (r : STM A) : STM A := TODO. *)
Definition check (b : bool) : STM void := if b then Ret ghost else retry.

Definition getSTM {A} (v : vector A) (i : int) : STM A := trigger (igetSTM v i).
Definition isEmptySTM  {A} (v : vector A) : STM bool := trigger (iisEmptySTM v).

Crane Extract Inlined Constant STM => "%t0".
Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })". (* Should this be incorported into the c++? *)
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
(* Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)". *)

Crane Extract Inlined Constant getSTM => "%a0.at(%a1)".
Crane Extract Inlined Constant isEmptySTM => "%a0.empty()".

End STM.
Import STM.

Module TVar.
Import STM_axioms.

Axiom TVar : Type -> Type.
Module TVar_axioms.
  Axiom inewTVar : forall {A}, A -> iSTM (TVar A).
  (* Axiom newTVarIO : forall {A}, A -> IO (TVar A). *)
  Axiom ireadTVar : forall {A}, TVar A -> iSTM A.
  Axiom iwriteTVar : forall {A}, TVar A -> A -> iSTM void.

End TVar_axioms.

Crane Extract Skip Module TVar_axioms.
Import TVar_axioms.

Definition newTVar {A} (a : A) : STM (TVar A) := trigger (inewTVar a).
Definition readTVar {A} (v : TVar A) : STM A  := trigger (ireadTVar v).
Definition writeTVar {A} (v : TVar A) (a : A) : STM void := trigger (iwriteTVar v a).

Crane Extract Inlined Constant TVar => "bsl::shared_ptr<stm::TVar<%t0>>" From "mini_stm.h".
Crane Extract Inlined Constant newTVar => "stm::newTVar<%t0>(%a0)".
Crane Extract Inlined Constant readTVar => "stm::readTVar<%t0>(%a0)".
Crane Extract Inlined Constant writeTVar => "stm::writeTVar<%t0>(%a0, %a1)".

End TVar.
Import TVar.

Definition modifyTVar {A : Type} (a : TVar A) (f : A -> A) : STM void :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret ghost.

Export STM TVar.
