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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

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

#[export] Instance stmVecE_mapping (T : Type) : TypeMapping (stmVecE T) :=
  event_family []
    [event (Ref (@GetSTM)) "%a0.at(%a1)";
     event (Ref (@IsEmptySTM)) "%a0.empty()"].
#[export] Instance stmControlE_mapping (T : Type) : TypeMapping (stmControlE T) :=
  event_family []
    [event (Ref (@Retry)) "stm::retry<%t0>()"].

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

#[export] Instance atomically_mapping : OperationMapping (Ref (@atomically)) :=
  effect_cpp [] ["t"]
    (Expr "stm::atomically([&] { return %arg(t); })").
#[export] Instance or_else_mapping : OperationMapping (Ref (@or_else)) :=
  effect_cpp [] ["t1"; "t2"]
    (Structured (Call "stm::orElse" [TypeParameter "A"] [Arg "t1"; Arg "t2"])).
#[export] Instance retry_mapping : OperationMapping (Ref (@retry)) :=
  effect_cpp [] []
    (Structured (Call "stm::retry" [TypeParameter "A"] [])).
(* At the TVar's element type, which a lambda's own closure type is not. *)
#[export] Instance new_tvar_mapping : OperationMapping (Ref (@new_tvar)) :=
  effect_args [] (uses Take ["a"])
    (Structured (Call "stm::newTVar" [TypeParameter "A"] [Arg "a"])).
#[export] Instance get_stm_mapping : OperationMapping (Ref (@get_stm)) :=
  effect_cpp [] ["v"; "i"]
    (Structured (Method (Arg "v") "at" [Arg "i"])).
#[export] Instance is_empty_stm_mapping : OperationMapping (Ref (@is_empty_stm)) :=
  effect_cpp [] ["v"]
    (Structured (Method (Arg "v") "empty" [])).

Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

Definition modify_tvar {A : Type} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- read_tvar a ;;
  write_tvar a (f val) ;;
  Ret tt.
