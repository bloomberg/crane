(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Clock effects for the standard library flavor.

   Re-exports shared definitions from [ClockDefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::chrono]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.ClockDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance clockE_mapping (T : Type) : TypeMapping (clockE T) :=
  event_family ["chrono"]
    [event (Ref (@SteadyNow)) "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count())";
     event (Ref (@SystemNow)) "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count())"].

#[export] Instance steady_now_mapping : OperationMapping (Ref (@steady_now)) :=
  effect_cpp ["chrono"] []
    (Structured (Convert Exact (Int I64) (Method (Call "std::chrono::duration_cast" [Name "std::chrono::milliseconds"] [Method (Call "std::chrono::steady_clock::now" [] []) "time_since_epoch" []]) "count" []))).
#[export] Instance system_now_mapping : OperationMapping (Ref (@system_now)) :=
  effect_cpp ["chrono"] []
    (Structured (Convert Exact (Int I64) (Method (Call "std::chrono::duration_cast" [Name "std::chrono::milliseconds"] [Method (Call "std::chrono::system_clock::now" [] []) "time_since_epoch" []]) "count" []))).
#[export] Instance now_mapping : OperationMapping (Ref (@now)) :=
  effect_cpp ["chrono"] []
    (Structured (Convert Exact (Int I64) (Method (Call "std::chrono::duration_cast" [Name "std::chrono::milliseconds"] [Method (Call "std::chrono::system_clock::now" [] []) "time_since_epoch" []]) "count" []))).
