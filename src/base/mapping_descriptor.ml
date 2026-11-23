(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The OCaml mirror of the typed mapping descriptors of
    [theories/Mapping/Descriptor.v] (Reference Manual, Typed mappings).  One
    OCaml type per Rocq inductive or record, one constructor or field per
    Rocq constructor or field, in the same order; Rocq [CamelCase]
    constructors are spelled [Snake_case].  Strings are the decoded
    [PrimString.string] leaves; [nat] fields are [int]; a Rocq type
    ([SourceType T], [KnownType T]) stays a closed, evar-free [Constr.t].

    {!Mapping_decode} builds these from a resolved instance,
    {!Mapping_validate} checks them, {!Mapping_discovery} finds and caches
    them. *)

(** [Ref d]: the declaration [d] by identity, never unfolded.  [d] is a
    reference applied to [parameters] (empty for a bare reference): [Ref
    (@Some nat)] is [Some] with parameter [nat]. *)
type declaration = { reference : Names.GlobRef.t; parameters : Constr.t list }

module Cpp = struct
  type type_expr =
    | Name of string
    | Apply of string * type_argument list
    | Source_type of Constr.t
    | Stored_component of string
    | Pointer of type_expr
    | Const of type_expr
    | Unsafe_verbatim of string

  and type_argument = Type_arg of type_expr | Value_arg of string
end

type construction = Expr of string | With_body of string * string

type copy_model =
  | Bit_copy
  | Retain_identity
  | Duplicate_value
  | Copy_components of string list
  | Unknown_copy

type read_style =
  | Read_by_value
  | Read_by_const_reference
  | Read_by_components of string list

type handle_pass = Handle_by_value | Handle_by_const_reference

type physical_parameter =
  | Canonical_by_value
  | Canonical_by_const_reference
  | Canonical_by_mutable_reference
  | Exact_parameter of string

type explicit_access_spec = {
  explicit_read : physical_parameter;
  explicit_write : physical_parameter option;
  explicit_replace : physical_parameter option;
}

type access_model =
  | Read_only_value of read_style
  | Mutable_value of read_style
  | Read_only_handle of handle_pass
  | Mutable_handle of handle_pass
  | Explicit_access of explicit_access_spec

type value_model = Structural | Identity | Unspecified

type lifetime_model =
  | Native_raii
  | Region_owned of declaration
  | Externally_owned
  | Manual_shared of declaration * declaration  (** retain, release *)

type release_plan = Ordinary_release | Drain_with of string

type view_mode = Read_only_view | Writable_view

type view_escape = Materialise_view of construction | Borrow_only

(** [ViewSpec T mode]; the mode is the Rocq index, recorded here. *)
type view_spec = {
  view_mode : view_mode;
  view_headers : string list;
  view_cpp : Cpp.type_expr;
  view_from_canonical : string;
  view_escape : view_escape;
}

type views =
  | No_views
  | Read_views of view_spec
  | Read_write_views of view_spec * view_spec * string
      (** read view, writable view, [read_from_write] *)

type component_type =
  | Known_type of Constr.t
  | Field_type of declaration * int  (** constructor, field *)

type component = { component_name : string; component_type : component_type }

type projection =
  | Owned_projection of string
  | Canonical_borrow_projection of string
  | Read_view_projection of string

type observation_requirement = Preferred_observation | Canonical_observation

type constructor_view = {
  view_requirement : observation_requirement;
  case_test : string;
  case_fields : (int * projection) list;
}

type constructor_mapping = {
  ctor_source : declaration;
  ctor_build : construction;
  ctor_view : constructor_view option;
}

type type_interface =
  | Abstract_interface
  | Algebraic_interface of constructor_mapping list

type numeral_action =
  | Numeral_zero
  | Numeral_one
  | Numeral_successor of int
  | Numeral_double of int
  | Numeral_double_plus_one of int
  | Numeral_identity of int
  | Numeral_negate of int

type numeral_case = {
  numeral_constructor : declaration;
  numeral_action : numeral_action;
}

type numeral_emitter =
  | Integer_token of string * string  (** prefix, suffix *)
  | Decimal_constructor of string

type numeral_spec = {
  numeral_cases : numeral_case list;
  numeral_emitter : numeral_emitter;
  numeral_converters : declaration list;
}

type type_mapping = {
  type_headers : string list;
  type_cpp : Cpp.type_expr;
  type_components : component list;
  type_copy : copy_model;
  type_access : access_model;
  type_views : views;
  type_interface : type_interface;
  type_model : value_model;
  type_lifetime : lifetime_model;
  type_release : release_plan;
  type_numerals : numeral_spec option;
}

type input_use =
  | Ignore
  | Read
  | Read_canonical
  | Write
  | Write_canonical
  | Take
  | Replace
  | Opaque_use

type argument_spec = { argument_name : string; argument_use : input_use }

type component_path = { path_argument : string; path_components : string list }

type initial_multiplicity = Initialise_once | Initialise_many

type component_initialiser = {
  initial_component : string;
  initial_source_argument : string option;
  initial_multiplicity : initial_multiplicity;
}

type borrow_form = Canonical_borrow | Read_view_borrow | Writable_view_borrow

type result_spec =
  | Return_value
  | Return_borrowed of borrow_form * component_path
  | Return_same_identity of string
  | Return_fresh_identity of component_initialiser list
  | Return_opaque

type operation_fact =
  | Reads_component of component_path
  | Writes_component of component_path * string option
  | Invalidates_element_borrows of component_path
  | Invalidates_views of component_path
  | Retains_argument of string * component_path
  | Releases_identity of string
  | External_effect of string

type operation_contract =
  | Pure_operation of argument_spec list * result_spec * operation_fact list
  | Effectful_operation of
      argument_spec list * result_spec * operation_fact list
  | Opaque_operation

type operation_mapping = {
  operation_headers : string list;
  operation_cpp : construction;
  operation_contract : operation_contract;
}
