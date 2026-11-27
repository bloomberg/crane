(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrency effects for the standard library flavor.

   Re-exports shared definitions from [ThreadDefs.v] and adds C++
   extraction mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.IO.
From Crane Require Export Monads.ThreadDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance threadE_mapping (T : Type) : TypeMapping (threadE T) :=
  event_family ["thread"; "chrono"]
    [event (Ref (@Join)) "%a0.wait()";
     event (Ref (@Sleep)) "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))"].

(* A [thread] is a value: copied, kept in data, joined any number of times or
   never.  [std::async]'s shared future has those semantics: [wait] joins, as
   often as asked, and the last copy released waits for the thread.  The
   function's result, if any, is dropped. *)
#[export] Instance thread_mapping : TypeMapping (thread) :=
  value_type ["future"] (Apply "std::shared_future" [TypeArg (Name "void")]) UnknownCopy.
#[export] Instance spawn_mapping : OperationMapping (Ref (@spawn)) :=
  effect_args ["future"; "utility"] (uses Take ["f"; "a"])
    (Expr "std::async(std::launch::async, [](auto f, auto a) { f(std::move(a)); }, %arg(f), %arg(a)).share()").
#[export] Instance join_mapping : OperationMapping (Ref (@join)) :=
  effect_cpp [] ["t"]
    (Structured (Method (Arg "t") "wait" [])).
#[export] Instance sleep_mapping : OperationMapping (Ref (@sleep)) :=
  effect_cpp ["thread"; "chrono"] ["d"]
    (Structured (Call "std::this_thread::sleep_for" [] [Build (Name "std::chrono::milliseconds") [Arg "d"]])).
