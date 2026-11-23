(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled type mappings: what the pipeline reads
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
  | Parameter of int  (** the head's type argument [i], from 0, counting type parameters only *)
  | Pointer of type_expr
  | Const of type_expr
  | Verbatim of string  (** [UnsafeVerbatim] *)

and argument = Type of type_expr | Value of string

type view = {
  requirement : observation_requirement;
  test : string;  (** a match condition over [%scrut] *)
  fields : (int * projection) list;  (** templates compiled *)
  field_types : (int * string) list;
      (** a field whose C++ type the plan spells, and its spelling in the
          legacy vocabulary: [%tN] for a field declared at one of the head's
          type parameters, [%ty] (the matched value's type) for a recursive
          field; a projection's [%ret] is compiled to it *)
  field_heads : (int * Names.GlobRef.t) list;
      (** a field of another inductive type, applied to no argument:
          spelled as that type's typed mapping writes it, where it has one *)
}

type constructor = {
  source : Names.constructor;
  build : string;  (** a term or block template *)
  view : view option;
}

type interface = Abstract | Algebraic of constructor list

(** A read view or a writable view. *)
type view_kind = Read_view | Write_view

(** Whether a view escaping its owner is copied into a canonical value, by
    a term template of [%a0], the view; or may not escape. *)
type escape = Materialise of string | Borrow_only

type view_plan = {
  view_type : type_expr;
  from_canonical : string;
      (** a term template of [%a0], a live canonical lvalue ([%value]) *)
  escape : escape;
  view_headers : string list;
}

(** No view, a read view, or a read and a writable view. *)
type views = {
  read : view_plan option;
  write : view_plan option;
  read_from_write : string option;
      (** narrows the writable view [%a0] to the read view *)
}

(** A numeral descriptor compiled: the action of each
    numeral constructor, by its index from 1. *)
type numerals = {
  cases : (int * numeral_action) list;
  emitter : numeral_emitter;
  converters : Names.GlobRef.t list;
}

type t = {
  instance : Names.GlobRef.t;
  head : Names.GlobRef.t;
  canonical : type_expr;
  components : (string * int) list;
      (** name, and the position of its parameter among the type arguments
          of a use (an instance or a value parameter takes none) *)
  component_binders : (string * int) list;
      (** name, and the position of its parameter among all the binders of
          the head, as the Rocq type applies them *)
  copy : copy_model;
  access : access_model;
  value_model : value_model;
  lifetime : lifetime_model;
  release : release_plan;
  interface : interface;
  views : views;
  headers : string list;  (** the views' headers included *)
  numerals : numerals option;
}

(** Whether [g] heads a type with a [TypeMapping] instance. *)
val is_type_head : Names.GlobRef.t -> bool

(** Rocq's primitive string type, where a typed mapping maps it. *)
val mapped_prim_string : unit -> Names.GlobRef.t option

(** Whether [g] is a mapped head or a constructor of one: what the legacy
    tables would call custom. *)
val is_mapped : Names.GlobRef.t -> bool

(** Whether [s] names the canonical type of a compiled plan whose copy
    model neither copies bits nor copies components ({!copies_cheaply}
    false at any arguments): an instantiated type ([External (s, _)])
    no longer names its head, so this is what tells a reader that
    [mpz_class] or [std::string] is not a literal type. *)
val duplicates_name : string -> bool

(** Every plan this extraction has compiled. *)
val compiled : unit -> t list

(** The numeral converters the instance mapping [g] declares, resolved
    without compiling or caching its plan; none where [g] has no instance
    that applies uniformly, or it fails to compile. *)
val numeral_converters : Names.GlobRef.t -> Names.GlobRef.t list

(** The plan of a mapped head (or of a constructor's inductive); a user error
    when no instance applies uniformly to the head's parameters, or the
    instance uses what this stage does not compile. *)
val find : Names.GlobRef.t -> t

(** The canonical C++ type of [p] at the type arguments [tys]. *)
val cpp_type : t -> 'p Cpp_ir.Type.t list -> 'p Cpp_ir.Type.t

(** [e], a type of the plan, at the type arguments [tys]. *)
val instantiate : type_expr -> 'p Cpp_ir.Type.t list -> 'p Cpp_ir.Type.t

(** The view of kind [k] [p] declares, if any. *)
val view : t -> view_kind -> view_plan option

val has_view : t -> view_kind -> bool

(** The type of [p]'s view [k] at the type arguments [tys]; an anomaly when
    [p] declares no such view. *)
val view_type : t -> view_kind -> 'p Cpp_ir.Type.t list -> 'p Cpp_ir.Type.t

(** The type arguments a type of [p]'s view [k] was instantiated at, read
    back from it, as far as the view type names them ([Any] for the
    others); [None] when it is not an instance of the view type. *)
val view_arguments : t -> view_kind -> 'p Cpp_ir.Type.t -> 'p Cpp_ir.Type.t list option

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

(** A physical parameter form the access model asks for, when
    it is not the canonical read form ([As_read]). *)
type physical =
  | As_read
  | Physical_value
  | Physical_const_reference
  | Physical_mutable_reference
  | Physical_view of view_kind  (** the view, by value *)

(** The canonical write-through form of [p]: [T&] for a
    mutable value, the read form for a handle (writing through a handle
    does not need to reseat it), and [explicit_write] for [ExplicitAccess]
    ([ExactParameter] is not supported and falls back to the read form). *)
val write_through : t -> physical

(** The form a parameter of [p] whose representation may be replaced takes:
    [T&], or [explicit_replace] for [ExplicitAccess]. *)
val replace_form : t -> physical

(** The headers of the mapped head [g], or of the inductive of the mapped
    constructor [g]. *)
val headers : Names.GlobRef.t -> string list

(** Record that a type of the head [g] was written: its headers are
    included ({!instantiated_headers}). *)
val note_instantiated : Names.GlobRef.t -> unit

(** The headers of every head {!note_instantiated} recorded. *)
val instantiated_headers : unit -> string list
