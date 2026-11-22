(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** CppIR at the phase that may still owe resolution a decision
    ({!Representation_obligation}): what lowering builds and CppIR
    finishing ({!Cpp_passes.Pipeline}) rewrites. *)

(** The phase index of a lowered value. *)
type phase = Grammar.lowered

module Type = struct
  (** A lowered type. *)
  type t = phase Type.t
end

module Expr = struct
  (** A lowered expression. *)
  type t = phase Expr.t
end

module Stmt = struct
  (** A lowered statement. *)
  type t = phase Stmt.t
end

module Decl = struct
  (** A lowered declaration. *)
  type t = phase Decl.t
end

module Arrows = struct
  (** A lowered callable's grouping. *)
  type t = phase Arrows.t
end

module Value_type = struct
  (** The type of a lowered expression. *)
  type t = phase Value_type.t
end

module Slot_type = struct
  (** What a lowered position asks of its value. *)
  type t = phase Slot_type.t
end

module Coercion = struct
  (** A lowered coercion. *)
  type t = phase Coercion.t

  (** A lowered coercion's plan. *)
  type plan = phase Coercion.plan
end
