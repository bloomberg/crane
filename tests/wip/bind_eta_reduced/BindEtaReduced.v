(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Bug: When the continuation of a bind is eta-reduced (just a function
   variable instead of [fun x => f x]), the bind result is discarded and
   the function is returned directly instead of being applied.

   Example: [line <- get_line ;; f line] should produce
     [std::string line = ...; return f(line);]
   but Coq eta-reduces [fun line => f line] to just [f], causing
   the generated C++ to be
     [get_line_iife(); return f;]  — WRONG
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module BindEtaReduced.

  (** Bug case 1: bind with a callback as continuation.
      [get_line] is bound, then [f] is applied to the result.
      Coq reduces [fun line => f line] to [f], breaking the bind. *)
  Definition with_line (f : string -> itree ioE string) : itree ioE string :=
    line <- get_line ;;
    f line.

  (** Bug case 2: same with a pure callback. *)
  Definition transform (f : string -> string) : itree ioE string :=
    line <- get_line ;;
    Ret (f line).

  (** Control case: explicit lambda prevents eta-reduction. *)
  Definition with_line_explicit (f : string -> itree ioE string) : itree ioE string :=
    line <- get_line ;;
    let r := f line in
    r.

End BindEtaReduced.

Crane Extraction "bind_eta_reduced" BindEtaReduced.
