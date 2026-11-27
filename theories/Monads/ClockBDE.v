(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Clock effects for the BDE flavor.

   Re-exports shared definitions from [ClockDefs.v] and adds C++ extraction
   mappings targeting BDE ([bsls::SystemTime]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.ClockDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance clockE_mapping (T : Type) : TypeMapping (clockE T) :=
  event_family ["bsls_systemtime.h"]
    [event (Ref (@SteadyNow)) "static_cast<int64_t>(bsls::SystemTime::nowMonotonicClock().totalMilliseconds())";
     event (Ref (@SystemNow)) "static_cast<int64_t>(bsls::SystemTime::nowRealtimeClock().totalMilliseconds())"].

#[export] Instance steady_now_mapping : OperationMapping (Ref (@steady_now)) :=
  effect_cpp ["bsls_systemtime.h"] []
    (Structured (Convert Exact (Int I64) (Method (Call "bsls::SystemTime::nowMonotonicClock" [] []) "totalMilliseconds" []))).
#[export] Instance system_now_mapping : OperationMapping (Ref (@system_now)) :=
  effect_cpp ["bsls_systemtime.h"] []
    (Structured (Convert Exact (Int I64) (Method (Call "bsls::SystemTime::nowRealtimeClock" [] []) "totalMilliseconds" []))).
#[export] Instance now_mapping : OperationMapping (Ref (@now)) :=
  effect_cpp ["bsls_systemtime.h"] []
    (Structured (Convert Exact (Int I64) (Method (Call "bsls::SystemTime::nowRealtimeClock" [] []) "totalMilliseconds" []))).
