(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events for the standard
   library flavor.

   Re-exports shared definitions from [STMDefs.v] and adds C++ extraction
   mappings targeting the standard library.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.IO External.Vector.
From Crane Require Export Monads.STMDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** [tvarE] events: the [stm_adapter.h] free
    functions on the current transaction. *)
#[export] Instance tvarE_mapping (T : Type) : TypeMapping (tvarE T) :=
  event_family ["stm_adapter.h"]
    [event (Ref (@NewTVar)) "stm::newTVar(%a0)";
     event (Ref (@ReadTVar)) "stm::readTVar(%a0)";
     event (Ref (@WriteTVar)) "stm::writeTVar(%a0, %a1)"].

(** [TVar] is [stm::TVar], a reference-counted
    handle, so copies share one variable. *)
#[export] Instance TVar_mapping (A : Type) : TypeMapping (TVar A) :=
  value_type ["stm_adapter.h"] (Apply "stm::TVar" [TypeArg (SourceType A)]) UnknownCopy.

(** [read_tvar] is [stm::readTVar]. *)
#[export] Instance read_tvar_mapping : OperationMapping (Ref (@read_tvar)) :=
  effect_cpp [] ["v"]
    (Structured (Call "stm::readTVar" [] [Arg "v"])).
(** [write_tvar] is [stm::writeTVar], taking ownership of the new value. *)
#[export] Instance write_tvar_mapping : OperationMapping (Ref (@write_tvar)) :=
  effect_args [] (uses ReadCanonical ["v"] ++ uses Take ["a"])
    (Structured (Call "stm::writeTVar" [] [Arg "v"; Arg "a"])).
