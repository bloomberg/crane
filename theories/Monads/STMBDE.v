(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events for the BDE flavor.

   Re-exports shared definitions from [STMDefs.v] and adds C++ extraction
   mappings targeting BDE.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.IOBDE External.VectorBDE.
From Crane Require Export Monads.STMDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance tvarE_mapping (T : Type) : TypeMapping (tvarE T) :=
  event_family ["stm_adapter.h"]
    [event (Ref (@NewTVar)) "stm::newTVar(%a0)";
     event (Ref (@ReadTVar)) "stm::readTVar(%a0)";
     event (Ref (@WriteTVar)) "stm::writeTVar(%a0, %a1)"].

#[export] Instance TVar_mapping (A : Type) : TypeMapping (TVar A) :=
  value_type ["stm_adapter.h"] (Apply "stm::TVar" [TypeArg (SourceType A)]) UnknownCopy.

#[export] Instance read_tvar_mapping : OperationMapping (Ref (@read_tvar)) :=
  effect_cpp [] ["v"]
    (Structured (Call "stm::readTVar" [] [Arg "v"])).
#[export] Instance write_tvar_mapping : OperationMapping (Ref (@write_tvar)) :=
  effect_args [] (uses ReadCanonical ["v"] ++ uses Take ["a"])
    (Structured (Call "stm::writeTVar" [] [Arg "v"; Arg "a"])).
