(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Parallel computation effects for the standard library flavor.

   Re-exports shared definitions from [ParDefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.ParDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(* A [future] is a value: copied, kept in data, read any number of times.  A
   [std::shared_future] is that; a [std::future] is read once and moved. *)
#[export] Instance parE_mapping (T : Type) : TypeMapping (parE T) :=
  event_family []
    [event (Ref (@MkThread)) "std::async(std::launch::async, %a0, %a1).share()";
     event (Ref (@GetThread)) "%a0.get()"].

#[export] Instance future_mapping (A : Type) : TypeMapping (future A) :=
  value_type ["future"] (Apply "std::shared_future" [TypeArg (SourceType A)]) UnknownCopy.
#[export] Instance async_mapping : OperationMapping (Ref (@async)) :=
  effect_args [] (uses Take ["f"; "a"])
    (Structured (Method (Call "std::async" [] [Verbatim "std::launch::async"; Arg "f"; Arg "a"]) "share" [])).
