(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The type of a lowered expression ({!Grammar.Value_type}), and why only
    C++ knows one where lowering cannot say ({!Deduction}). *)

include Grammar.Value_type
module Deduction = Grammar.Deduction

(** The type a callable value has as a [Function] type, at its own
    grouping: a closure or a function name as the [crane::fn] it would be
    named. *)
let as_function_type : 'p t -> 'p Type.t option = function
  | Typed (Function _ as t) -> Some t
  | Closure a | Function_name (_, a) -> Some (Arrows.to_type a)
  | Typed _ | Never | Deduced _ -> None

(** The grouping a callable value is called at, where it is one. *)
let arrows : 'p t -> 'p Arrows.t option = function
  | Typed t -> Arrows.of_type t
  | Closure a | Function_name (_, a) -> Some a
  | Never | Deduced _ -> None

(** Whether lowering has not synthesised the type yet. *)
let not_yet_typed = function Deduced Not_yet_typed -> true | _ -> false

(** The reason a deduced type is deduced, for the census. *)
let deduction_name : Deduction.t -> string = function
  | Foreign_text -> "foreign text"
  | Runtime_helper _ -> "runtime helper"
  | Generic_lambda -> "generic lambda"
  | Requirement -> "requirement"
  | Not_yet_typed -> "not yet typed"
