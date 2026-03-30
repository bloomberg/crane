(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events.

   Provides axiomatized STM effects ([iSTM]) with smart constructors
   and C++ extraction mappings. Use [itree iSTM A] as the monadic type.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO External.Vector.

Open Scope itree_scope.

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
Export STM_axioms.

Definition atomically {A} (t : itree iSTM A) : itree iIO A :=
  translate (@iatomically) t.
Definition retry {A} : itree iSTM A := ITree.trigger (@iretry A).
Axiom orElse : forall {A}, itree iSTM A -> itree iSTM A -> itree iSTM A.
Definition check (b : bool) : itree iSTM unit :=
  if b then Ret tt else retry.

Definition getSTM {A} (v : vector A) (i : int) : itree iSTM A :=
  ITree.trigger (igetSTM v i).
Definition isEmptySTM {A} (v : vector A) : itree iSTM bool :=
  ITree.trigger (iisEmptySTM v).

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".

Crane Extract Inlined Constant getSTM => "%a0.at(%a1)".
Crane Extract Inlined Constant isEmptySTM => "%a0.empty()".

End STM.

Import STM.

Module TVar.
Import STM_axioms.

Axiom TVar : Type -> Type.
Module TVar_axioms.
  Axiom inewTVar : forall {A}, A -> iSTM (TVar A).
  Axiom ireadTVar : forall {A}, TVar A -> iSTM A.
  Axiom iwriteTVar : forall {A}, TVar A -> A -> iSTM unit.

End TVar_axioms.

Crane Extract Skip Module TVar_axioms.
Import TVar_axioms.

Definition newTVar {A} (a : A) : itree iSTM (TVar A) :=
  ITree.trigger (inewTVar a).
Definition readTVar {A} (v : TVar A) : itree iSTM A :=
  ITree.trigger (ireadTVar v).
Definition writeTVar {A} (v : TVar A) (a : A) : itree iSTM unit :=
  ITree.trigger (iwriteTVar v a).

Crane Extract Inlined Constant TVar => "std::shared_ptr<stm::TVar<%t0>>" From "mini_stm.h".
Crane Extract Inlined Constant newTVar => "stm::newTVar<%t0>(%a0)".
Crane Extract Inlined Constant readTVar => "%a0->read()".
Crane Extract Inlined Constant writeTVar => "%a0->write(%a1)".

End TVar.

Import TVar.

Definition modifyTVar {A : Type} (a : TVar A) (f : A -> A) : itree iSTM unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.

Export STM TVar.
