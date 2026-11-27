(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrency effects for the BDE flavor.

   Re-exports shared definitions from [ThreadDefs.v] and adds C++
   extraction mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.IOBDE.
From Crane Require Export Monads.ThreadDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance threadE_mapping (T : Type) : TypeMapping (threadE T) :=
  event_family ["bsl_thread.h"; "chrono"]
    [event (Ref (@Join)) "%a0.join()";
     event (Ref (@Sleep)) "bsl::this_thread::sleep_for(std::chrono::milliseconds(%a0))"].

#[export] Instance thread_mapping : TypeMapping (thread) :=
  value_type ["bsl_thread.h"] (Name "bsl::thread") UnknownCopy.
#[export] Instance spawn_mapping : OperationMapping (Ref (@spawn)) :=
  effect_args ["bsl_thread.h"] (uses Take ["f"; "a"])
    (Structured (Build (Name "bsl::thread") [Arg "f"; Arg "a"])).
#[export] Instance join_mapping : OperationMapping (Ref (@join)) :=
  effect_cpp [] ["t"]
    (Structured (Method (Arg "t") "join" [])).
#[export] Instance sleep_mapping : OperationMapping (Ref (@sleep)) :=
  effect_cpp ["bsl_thread.h"; "chrono"] ["d"]
    (Structured (Call "bsl::this_thread::sleep_for" [] [Build (Name "std::chrono::milliseconds") [Arg "d"]])).
