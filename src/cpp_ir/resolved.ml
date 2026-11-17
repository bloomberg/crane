(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** CppIR at the phase that owes resolution nothing: no type without a C++
    spelling, no unsettled callable constraint, no undecided capture or
    [constexpr], no uninstantiated mapping block.  The forms that would say
    otherwise exist only at {!Grammar.lowered}, so they cannot occur here.
    {!Cpp_passes.Pipeline} produces it, at the end of CppIR finishing and for the
    few types and values written outside every declaration; the printer and
    {!Cpp_ast}'s leaves read it, and name no lowered value. *)

(** The phase index of a resolved value. *)
type phase = Grammar.resolved

module Type = struct
  (** A resolved type. *)
  type t = phase Type.t
end

module Expr = struct
  (** A resolved expression. *)
  type t = phase Expr.t
end

module Stmt = struct
  (** A resolved statement. *)
  type t = phase Stmt.t
end

module Decl = struct
  (** A resolved declaration. *)
  type t = phase Decl.t
end
