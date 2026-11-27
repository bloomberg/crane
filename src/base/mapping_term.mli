(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An operation mapping's structured body ([Structured], a
    [Crane.Cpp.Term]) compiled: its arguments resolved to the positions a
    call supplies them at, its [LetIn]s substituted, its types resolved, and
    its [Wrapping] and [Saturating] operators spelled.

    Conversions are folded where the types and literals are known:
    {ul
    {- R1: a conversion of an integer literal is the literal of the target
       type, its value converted ([Wrap] modulo two to the width,
       [Saturate] clamped); an [Exact] one that does not fit is the
       mapping's error;}
    {- R2: a conversion to the integer type its operand has is the operand;}
    {- R3: [Convert k A (Convert Exact B e)] is [Convert k A e] where [B]
       holds every value of [e]'s type.  Never through [Wrap].}}
    An argument's integer type is known where its mapped type's canonical
    type is written [Int t] ({!Mapping_plan.t.integer}). *)

open Mapping_descriptor

type ty =
  | Int of Cpp_ir.Integer_type.t
  | Bool
  | Float64
  | Result  (** the type the use yields *)
  | Plan of Mapping_plan.type_expr  (** [Parameter i] is the call's type argument [i] *)

type t =
  | Arg of int  (** the argument at this position among a call's *)
  | Lit of Cpp_ir.Integer_type.t * Z.t
  | Bool_lit of bool
  | String_lit of string
  | Unop of Cpp.unop * t
  | Binop of Cpp.binop * t * t  (** an arithmetic operator only [Unchecked] *)
  | Cond of t * t * t
  | Convert of Cpp.conversion * ty * t
  | Call of string * ty list * t list
  | Method of t * string * t list
  | Member of t * string
  | Index of t * t
  | Build of ty * t list
  | Enum_value of ty * string
  | Verbatim of string

(** The integer type of [e], where every platform agrees on it. *)
val type_of : arg_type:(int -> Cpp_ir.Integer_type.t option) -> t -> Cpp_ir.Integer_type.t option

(** [body] compiled: [arg x] is the position of argument [x], [ty] resolves
    a type; [fail] reports the mapping's error. *)
val resolve :
  fail:(Pp.t -> unit) ->
  arg:(string -> int) ->
  ty:(Cpp.type_expr -> ty) ->
  arg_type:(int -> Cpp_ir.Integer_type.t option) ->
  result_type:Cpp_ir.Integer_type.t option ->
  Cpp.term ->
  t

(** [e] with R1-R3 applied bottom up.  [arg_literal i] is the value of the
    argument at position [i] where a use supplies a literal. *)
val fold :
  fail:(Pp.t -> unit) ->
  arg_type:(int -> Cpp_ir.Integer_type.t option) ->
  ?arg_literal:(int -> Z.t option) ->
  t ->
  t

(** [e] in the term-template vocabulary ([%aN], [%tN], [%ret]), an operator's
    operand parenthesised unless it binds tighter: what the readers of a
    mapping's text read. *)
val text : t -> string
