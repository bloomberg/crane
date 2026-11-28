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

(** A transactional variable; opaque in Rocq, [stm::TVar] in C++. *)
Axiom TVar : Type -> Type.

(** Transactional variable operations, meaningful only inside [atomically]. *)
Inductive tvarE : Type -> Type :=
(** Allocate a variable holding the given value. *)
| NewTVar : forall {A}, A -> tvarE (TVar A)
(** Read a variable, logging it in the transaction's read set. *)
| ReadTVar : forall {A}, TVar A -> tvarE A
(** Write a variable; visible to other threads
    only once the transaction commits. *)
| WriteTVar : forall {A}, TVar A -> A -> tvarE unit.

(** Read-only vector queries usable inside a transaction. *)
Inductive stmVecE : Type -> Type :=
(** The element at an index; out of range throws ([at]). *)
| GetSTM : forall {A}, vector A -> int -> stmVecE A
(** Whether the vector is empty. *)
| IsEmptySTM : forall {A}, vector A -> stmVecE bool.

(** Transaction control. *)
Inductive stmControlE : Type -> Type :=
(** Abandon the transaction and rerun it once a variable it read changes. *)
| Retry : forall A, stmControlE A.

(** [stmVecE] events: the vector's [at] and [empty]. *)
#[export] Instance stmVecE_mapping (T : Type) : TypeMapping (stmVecE T) :=
  event_family []
    [event (Ref (@GetSTM)) "%a0.at(%a1)";
     event (Ref (@IsEmptySTM)) "%a0.empty()"].
(** [Retry] is [stm::retry], which throws to the enclosing [atomically]. *)
#[export] Instance stmControlE_mapping (T : Type) : TypeMapping (stmControlE T) :=
  event_family []
    [event (Ref (@Retry)) "stm::retry<%t0>()"].

(** The events of a transaction body. Only a Rocq abbreviation, never emitted. *)
Definition stmE := tvarE +' stmVecE +' stmControlE.
Crane Extract Skip stmE.

(** Run a transaction as one atomic step of an IO program. *)
Axiom atomically : forall {E} `{ioE -< E} {A}, itree stmE A -> itree E A.
(** Run [t1], falling back to [t2] if it retries. *)
Axiom or_else : forall {A}, itree stmE A -> itree stmE A -> itree stmE A.

(** A fresh variable initialized to [a]. *)
Definition new_tvar {E} `{tvarE -< E} {A} (a : A) : itree E (TVar A) := embed (NewTVar a).
(** The current value of [v] in this transaction. *)
Definition read_tvar {E} `{tvarE -< E} {A} (v : TVar A) : itree E A := embed (ReadTVar v).
(** Set [v] to [a] in this transaction. *)
Definition write_tvar {E} `{tvarE -< E} {A} (v : TVar A) (a : A) : itree E unit := embed (WriteTVar v a).

(** Block the transaction until something it read changes. *)
Definition retry {A} : itree stmE A := embed (Retry A).

(** Element [i] of [v]. *)
Definition get_stm {E} `{stmVecE -< E} {A} (v : vector A) (i : int) : itree E A := embed (GetSTM v i).
(** Whether [v] is empty. *)
Definition is_empty_stm {E} `{stmVecE -< E} {A} (v : vector A) : itree E bool := embed (IsEmptySTM v).

(** [atomically] is [stm::atomically] over a nullary lambda; the adapter
    keeps the transaction in a thread-local, so reads and writes take none. *)
#[export] Instance atomically_mapping : OperationMapping (Ref (@atomically)) :=
  effect_cpp [] ["t"]
    (Expr "stm::atomically([&] { return %arg(t); })").
(** [or_else] is [stm::orElse]. C++ evaluates both branches before the
    call, so a [retry] in [t1] retries the whole transaction rather than
    falling back to [t2]. *)
#[export] Instance or_else_mapping : OperationMapping (Ref (@or_else)) :=
  effect_cpp [] ["t1"; "t2"]
    (Structured (Call "stm::orElse" [TypeParameter "A"] [Arg "t1"; Arg "t2"])).
(** [retry] is [stm::retry] at the expected result type. *)
#[export] Instance retry_mapping : OperationMapping (Ref (@retry)) :=
  effect_cpp [] []
    (Structured (Call "stm::retry" [TypeParameter "A"] [])).
(** [new_tvar] is [stm::newTVar] at the TVar's element type, which a lambda's
    own closure type is not. *)
#[export] Instance new_tvar_mapping : OperationMapping (Ref (@new_tvar)) :=
  effect_args [] (uses Take ["a"])
    (Structured (Call "stm::newTVar" [TypeParameter "A"] [Arg "a"])).
(** [get_stm] is the vector's [at]. *)
#[export] Instance get_stm_mapping : OperationMapping (Ref (@get_stm)) :=
  effect_cpp [] ["v"; "i"]
    (Structured (Method (Arg "v") "at" [Arg "i"])).
(** [is_empty_stm] is the vector's [empty]. *)
#[export] Instance is_empty_stm_mapping : OperationMapping (Ref (@is_empty_stm)) :=
  effect_cpp [] ["v"]
    (Structured (Method (Arg "v") "empty" [])).

(** Proceed if [b] holds, else [retry]: a guard that waits for a condition. *)
Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

(** Apply [f] to the value of [a] in place. *)
Definition modify_tvar {A : Type} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- read_tvar a ;;
  write_tvar a (f val) ;;
  Ret tt.
