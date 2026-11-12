(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** CppIR at the phase that owes resolution nothing: no type without a C++
    spelling, no unsettled callable constraint, no undecided capture or
    [constexpr], no uninstantiated mapping block.  The forms that would say
    otherwise exist only at {!Grammar.lowered}, so they cannot occur here. *)

type phase = Grammar.resolved

module Type = struct
  type t = phase Type.t
end

module Expr = struct
  type t = phase Expr.t
end

module Stmt = struct
  type t = phase Stmt.t
end

module Decl = struct
  type t = phase Decl.t
end
