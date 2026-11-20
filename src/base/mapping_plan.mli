(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled type mappings (design 21.4, plan D3): what the pipeline reads
    of a [TypeMapping] instance.

    A plan is compiled once per mapped head, from the instance that maps the
    head applied to one fresh variable per parameter: the plan is generic,
    and a type argument of a use stands for the parameter it instantiates.
    A component's logical type must be one of the head's parameters (a
    [KnownType] or [SourceType] naming it, or a [FieldType] whose field is
    declared at it), so that its physical type at a use is the C++ type
    Crane chose for that type argument.

    Templates are compiled into the hole vocabulary of
    {!Cpp_ir.Foreign_template}: [%stored(x)] becomes the [%tN] of the
    parameter component [x] is, and an algebraic interface's case tests and
    projections become one match template.  The canonical type is never
    text: {!cpp_type} builds a structured CppIR type. *)

open Mapping_descriptor

type type_expr =
  | Name of string
  | Apply of string * argument list
  | Parameter of int  (** the head's type argument [i], from 0 *)
  | Pointer of type_expr
  | Const of type_expr
  | Verbatim of string  (** [UnsafeVerbatim] *)

and argument = Type of type_expr | Value of string

type view = {
  requirement : observation_requirement;
  test : string;  (** a match condition over [%scrut] *)
  fields : (int * projection) list;  (** templates compiled *)
}

type constructor = {
  source : Names.constructor;
  build : string;  (** a term or block template *)
  view : view option;
}

type interface = Abstract | Algebraic of constructor list

type t = {
  instance : Names.GlobRef.t;
  head : Names.GlobRef.t;
  canonical : type_expr;
  components : (string * int) list;  (** name, parameter *)
  copy : copy_model;
  access : access_model;
  value_model : value_model;
  lifetime : lifetime_model;
  release : release_plan;
  interface : interface;
  headers : string list;
}

(** Whether [g] heads a type with a [TypeMapping] instance. *)
val is_type_head : Names.GlobRef.t -> bool

(** Whether [g] is a mapped head or a constructor of one: what the legacy
    tables would call custom. *)
val is_mapped : Names.GlobRef.t -> bool

(** The plan of a mapped head (or of a constructor's inductive); a user error
    when no instance applies uniformly to the head's parameters, or the
    instance uses what this stage does not compile. *)
val find : Names.GlobRef.t -> t

(** The canonical C++ type of [p] at the type arguments [tys]. *)
val cpp_type : t -> 'p Cpp_ir.Type.t list -> 'p Cpp_ir.Type.t

(** The canonical type in the legacy type-template vocabulary
    ([std::optional<%t0>]), for the readers that reason about a mapping's
    text; the type itself is built by {!cpp_type}. *)
val type_text : t -> string

(** The build template of a mapped constructor; a user error for a
    constructor of an abstract type or one the interface does not map. *)
val constructor_template : Names.constructor -> string

(** The constructor templates of a mapped inductive, in constructor order. *)
val constructor_templates : Names.inductive -> string list

(** The match template of a mapped inductive, from its constructor views; a
    user error for an abstract type, a constructor without a view, or a
    [ReadViewProjection]. *)
val match_template : Names.inductive -> string

(** Whether copying a value of [p] is cheap, [argument i] saying whether
    copying its type argument [i] is: [BitCopy] is, [CopyComponents] is when
    each named component is, anything else is not. *)
val copies_cheaply : t -> argument:(int -> bool) -> bool

(** Whether a canonical read of [p] passes it by value, [argument i] saying
    whether type argument [i] is read by value: [ReadByValue] and
    [HandleByValue] do, [ReadByComponents] does when each named component
    is read by value, the reference forms do not. *)
val read_by_value : t -> argument:(int -> bool) -> bool

(** The headers of the mapped head [g], or of the inductive of the mapped
    constructor [g]. *)
val headers : Names.GlobRef.t -> string list

(** Record that a type of the head [g] was written: its headers are
    included ({!instantiated_headers}). *)
val note_instantiated : Names.GlobRef.t -> unit

(** The headers of every head {!note_instantiated} recorded. *)
val instantiated_headers : unit -> string list
