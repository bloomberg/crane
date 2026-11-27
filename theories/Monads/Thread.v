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

Crane Extract Inductive threadE => ""
  [ "%a0.wait()"
    "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))" ]
  From "thread" "chrono".

(* A [thread] is a value: copied, kept in data, joined any number of times or
   never.  [std::async]'s shared future has those semantics: [wait] joins, as
   often as asked, and the last copy released waits for the thread.  The
   function's result, if any, is dropped. *)
Crane Extract Inlined Constant thread => "std::shared_future<void>" From "future".
Crane Extract Inlined Constant spawn =>
  "std::async(std::launch::async, [](auto f, auto a) { f(std::move(a)); }, %a0, %a1).share()"
  From "future" "utility".
Crane Extract Inlined Constant join => "%a0.wait()".
Crane Extract Inlined Constant sleep =>
  "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))"
  From "thread" "chrono".
