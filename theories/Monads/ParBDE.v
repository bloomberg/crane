(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Parallel computation effects for the BDE flavor.

   Re-exports shared definitions from [ParDefs.v] and adds C++ extraction
   mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.ParDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance parE_mapping (T : Type) : TypeMapping (parE T) :=
  event_family ["bsl_future.h"]
    [event (Ref (@MkThread)) "bsl::async(bsl::launch::async, %a0, %a1)";
     event (Ref (@GetThread)) "%a0.get()"].

#[export] Instance future_mapping (A : Type) : TypeMapping (future A) :=
  value_type ["bsl_future.h"] (Apply "bsl::future" [TypeArg (SourceType A)]) UnknownCopy.
#[export] Instance async_mapping : OperationMapping (Ref (@async)) :=
  effect_args ["bsl_future.h"] (uses Take ["f"; "a"])
    (Structured (Call "bsl::async" [] [Verbatim "bsl::launch::async"; Arg "f"; Arg "a"])).
