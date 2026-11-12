(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** CppIR at the phase that may still owe resolution a decision
    ({!Representation_obligation}). *)

type phase = Grammar.lowered

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
