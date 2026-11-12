(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** CppIR: the structured C++ program, before names are resolved and
    declarations are scheduled.

    Every family is phase-indexed.  A [lowered] program may still owe
    decisions that resolution makes -- a type with no C++ spelling yet, a
    callable parameter whose constraint is unsettled, a lambda whose capture
    is not written, a definition not yet known to be [constexpr] or not, a
    mapping's block not yet instantiated.  Those forms exist only at
    [lowered]: a [resolved] value cannot hold one, and a match over one need
    not mention them.  Forms resolution introduces (a method call, an
    instantiated mapping, a tolerant cast) exist at both phases, since the
    passes that introduce them run between the two.

    The families are mutually recursive -- a type names a value argument, an
    expression names a type -- so they are defined here together, as
    recursive modules holding only types; each family's own file
    ([Cpp_ir.Type], [Cpp_ir.Expr], ...) re-exports it under its final
    name. *)

open Names

(** The phase of a program that may still owe resolution a decision. *)
type lowered = Lowered_phase

(** The phase of a program that owes resolution nothing. *)
type resolved = Resolved_phase

module rec Type_variable : sig
  (** A C++ type variable. *)
  type t =
    | Index of int * Id.t option
        (** The [i]th (from 1) type variable of the enclosing declaration's
            parameter list, with its parameter's name where that is known. *)
    | Named of Id.t
        (** A type variable known only by the name a template header
            declares it under: a lambda's own [_T1], a method's [_A0]. *)
end =
  Type_variable

and Erased_kind : sig
  (** What an erased position removed. *)
  type t =
    | Type
    | Proof
    | Implicit
end =
  Erased_kind

and Variant_storage : sig
  (** Where an inductive's alternatives live: inline in the value, or in a
      counted block the value points at. *)
  type t =
    | Inline
    | Shared
end =
  Variant_storage

and Reference_kind : sig
  (** [T&], or the forwarding reference [T&&] a deduced parameter takes. *)
  type t =
    | Lvalue
    | Forwarding
end =
  Reference_kind

and Type : sig
  (** A C++ type. *)
  type _ t =
    | Variable : Type_variable.t -> 'p t
    | Instance : Id.t * GlobRef.t -> 'p t
        (** A type-class instance template parameter and the class
            constraining it. *)
    | Promoted_member : Id.t -> 'p t
        (** A [Type]-valued type-class field lifted to an associated type. *)
    | Named : Id.t * 'p t list -> 'p t
        (** A local type identifier, for nested structs. *)
    | External : string * 'p t list -> 'p t
        (** A type named verbatim and never struct-qualified: a type from an
            included header, a builtin scalar, a struct local to a body. *)
    | Entity_application : GlobRef.t * 'p t list * 'p Expr.t list -> 'p t
        (** A global type applied to type and value arguments. *)
    | Function : 'p t list * 'p t -> 'p t
    | Const : 'p t -> 'p t
    | In_namespace : GlobRef.t * 'p t -> 'p t
    | Member : 'p t * Id.t -> 'p t  (** [typename Base<T>::nested] *)
    | Apply : 'p t * 'p t list -> 'p t  (** An alias template applied. *)
    | Reference : Reference_kind.t * 'p t -> 'p t
    | Erased : Erased_kind.t -> 'p t
    | Pointer : 'p t -> 'p t
    | Variant : Variant_storage.t * 'p t list -> 'p t
    | Shared_pointer : 'p t -> 'p t
    | Void : 'p t
    | Any : 'p t  (** [std::any], holding a value that is boxed. *)
    | Type_constructor : 'p t -> 'p t
        (** A type constructor named but not applied, at a template template
            argument. *)
    | Carrier_parameter : 'p t
        (** The parameter of the alias template a carrier abstraction
            introduces, standing where the carrier's argument goes. *)
    | Auto : 'p t
    | Decay : 'p t -> 'p t
    | Non_deduced : 'p t -> 'p t  (** [std::type_identity_t<T>] *)
    | Rebind : 'p t * 'p t -> 'p t  (** [crane::rebind_t<F, X>] *)
    | Type_of : 'p Expr.t -> 'p t  (** [decltype(e)], undecayed *)
    | Decltype_auto : 'p t
    | Foreign : 'p Foreign.t -> 'p t
        (** An inline mapping's type template instantiated at its use. *)
    | Obligation : Representation_obligation.t -> lowered t
        (** A type resolution has still to decide: one with no C++ type
            determined ({!Representation_obligation.Unresolved_type}), or one
            whose representation is unknown here
            ({!Representation_obligation.Opaque_type}). *)
end =
  Type

and Type_test : sig
  (** A compile-time question about types. *)
  type 'p t = Convertible of 'p Type.t * 'p Type.t
end =
  Type_test

and Precondition : sig
  (** A precondition carried over from a Rocq annotation. *)
  type t =
    | Checked of string  (** a C++ predicate, checked at run time *)
    | Stated of string  (** a statement C++ cannot spell, only written *)
end =
  Precondition

and Binary_operator : sig
  type t =
    | Equal
    | Not_equal
    | And
    | Or
    | Assign  (** [=] in expression position *)
end =
  Binary_operator

and Unary_operator : sig
  type t =
    | Not
    | Address_of
end =
  Unary_operator

and Allocation : sig
  (** Where an allocation's storage comes from. *)
  type t =
    | Heap
    | Arena_scoped
    | Reusing  (** Perceus reuse of a uniquely owned cell *)
end =
  Allocation

and Erase_shape : sig
  (** The erased representation a callable is adapted to. *)
  type 'p t =
    | Boxed_whole
    | At_signature of 'p Type.t
end =
  Erase_shape

and Access : sig
  (** How a member name attaches to the object in front of it. *)
  type t =
    | Dot
    | Arrow
end =
  Access

and Call : sig
  (** What lowering knew about a call. *)
  type 'p signature = {
    yields : 'p result;
    params : 'p params;
    constructs : GlobRef.t option;
        (** the constructor a factory call builds *)
    occurrence : Miniml.Occurrence.t option;
        (** the Core call the call is made of *)
  }

  (** What a call yields. *)
  and 'p result =
    | Yields of 'p Type.t
    | Untyped
        (** the callee has no Crane-level type; a consumer defers to C++
            deduction *)

  (** The callee's parameter types, aligned with the arguments. *)
  and 'p params =
    | Types of 'p Type.t list
    | Unknown
end =
  Call

and Written_capture : sig
  (** A lambda's capture as written. *)
  type t =
    | Nothing  (** [\[\]] *)
    | By_reference  (** [\[&\]] *)
    | By_copy of {
        this : bool;
        moved : Id.t list;
      }  (** [\[=\]], with [this] and the moved variables *)
end =
  Written_capture

and Capture : sig
  (** How a lambda holds what it names from its scope. *)
  type _ t =
    | Runs_in_place : lowered t
        (** It runs where it is written and borrows its scope; what it
            writes between the brackets is not yet decided. *)
    | Stored : lowered t
        (** It may outlive its scope and holds copies; what it writes is not
            yet decided. *)
    | Written : Written_capture.t -> 'p t
end =
  Capture

and Local_fixpoint : sig
  (** How the lambda of a local fixpoint is encoded. *)
  type encoding =
    | Self_passing of Id.t list
        (** It calls its group's members through these parameters, one per
            member, in the group's order: the knot its encoding ties. *)
    | Knot  (** It ties that knot for the fixpoint's callers, who call it. *)
    | Lowered
        (** Its control is lowered (a loop, or a machine with a stack of its
            own) and it calls itself through nothing. *)

  (** The local fixpoint whose body a lambda is. *)
  type t = {
    binder : Id.t;  (** the binder it binds in its definition *)
    name : Id.t;  (** the name it is called by in C++ *)
    member : Miniml.Occurrence.t * int;
        (** the Core fixpoint it lowers, by the fixpoint's occurrence, and
            the index of its function among the fixpoint's *)
    captured : (Id.t * Core_binder.t) list;
        (** the Core binder each local of the enclosing scope its Core
            fixpoint reads stands for, by the local's name *)
    encoding : encoding;
  }
end =
  Local_fixpoint

and Lambda : sig
  (** A lambda expression.  Its parameters are in source order. *)
  type 'p t = {
    params : ('p Type.t * Id.t option) list;
    type_params : Id.t list;
        (** template parameters of a polymorphic function object,
            [[]<typename X>(...)]; empty for an ordinary lambda *)
    return_type : 'p Type.t option;
    body : 'p Stmt.t list;
    capture : 'p Capture.t;
    moved : Id.t list;  (** what a stored lambda takes by move *)
    binders : (Id.t * Core_binder.t) list;
        (** the Core binder each parameter stands for, by the parameter's
            name, where the lambda is the body of a Core function *)
    fixpoint : Local_fixpoint.t option;
        (** the local fixpoint whose body this lambda is *)
  }
end =
  Lambda

and Method_call : sig
  (** A call of a function emitted as a member of its receiver's struct. *)
  type 'p t = {
    method_ : GlobRef.t;
    access : Access.t;
    receiver : 'p Expr.t;
    type_args : 'p Type.t list;
    args : 'p Expr.t list;
  }
end =
  Method_call

and Method_value : sig
  (** Such a function named as a value: a lambda calling it on its
      receiver. *)
  type 'p t = {
    method_ : GlobRef.t;
    access : Access.t;
    receiver : int;  (** the receiver's position among [params] *)
    params : 'p Type.t option list;
    type_args : 'p Type.t list;
  }
end =
  Method_value

and Projection : sig
  (** A record projection applied to its record, and to the rest of its
      arguments. *)
  type 'p t = {
    projection : GlobRef.t;
    record : 'p Expr.t;
    args : 'p Expr.t list;
  }
end =
  Projection

and Unbox : sig
  (** How a boxed value is read back. *)
  type 'p t =
    | To of 'p Type.t
    | Or_keep of 'p Type.t
    | List of 'p Type.t * 'p Type.t  (** the list, and its flat instantiation *)
end =
  Unbox

and Numeral : sig
  (** A numeral's value and how it is spelled. *)
  type t = {
    value : Z.t;
    text : string;
  }
end =
  Numeral

and Literal : sig
  type t =
    | String of Pstring.t
    | Uint63 of Uint63.t
    | Float of Float64.t
    | Bool of bool
    | Int of int
    | Null_pointer
end =
  Literal

and Aggregate : sig
  (** The aggregate initialisation of a struct value, [S<A>{args}].  The two
      ways differ in what names the struct:

      - an {!Expr.Aggregate} names a record struct by its global;
      - an {!Expr.Local_aggregate} names a struct by a local identifier, as
        a constructor struct nested in its inductive's is named. *)
  type ('name, 'p) t = {
    struct_ : 'name;
    type_args : 'p Type.t list;
    values : 'p Expr.t list;
  }
end =
  Aggregate

and Requires : sig
  (** A requires expression. *)
  type 'p t = {
    params : ('p Type.t * Id.t) list;
    constraints : ('p Expr.t * 'p Expr.t) list;
        (** each expression with the constraint on it *)
    type_requirements : 'p Type.t list;
  }
end =
  Requires

and Expr : sig
  (** A C++ expression. *)
  type _ t =
    | Local : Id.t -> 'p t
    | Entity : GlobRef.t * 'p Type.t list * 'p Foreign.custom option -> 'p t
    | Call : 'p Call.signature * 'p t * 'p t list -> 'p t
        (** what lowering knew about the call, the callee, and its arguments
            in source order *)
    | Converting_construct : 'p Type.t * 'p t list -> 'p t
    | Box : 'p Type.t * 'p t -> 'p t
    | Dereference : 'p t -> 'p t
    | Move : 'p t -> 'p t
    | Forward : 'p Type.t * 'p t -> 'p t
    | Lambda : 'p Lambda.t -> 'p t
    | Suspend : lowered Type.t * lowered t -> lowered t
        (** a coinductive value with its constructor suspended in a thunk,
            written by resolution as its type's [lazy_] factory applied to
            the thunk *)
    | Allocate : Allocation.t * 'p Type.t -> 'p t
    | Aggregate : (GlobRef.t, 'p) Aggregate.t -> 'p t
    | Local_aggregate : (Id.t, 'p) Aggregate.t -> 'p t
    | Member : 'p t * Id.t -> 'p t
    | Project : 'p t * GlobRef.t * 'p Type.t option -> 'p t
        (** a record field read through its projection *)
    | Literal : Literal.t -> 'p t
    | Persistent_array : 'p t array * 'p t -> 'p t
    | Requires : 'p Requires.t -> 'p t
    | Concept_application : GlobRef.t * GlobRef.t * 'p Type.t list -> 'p t
    | This : 'p t
    | Shared_from_this : 'p Type.t -> 'p t
    | Access : Access.t * 'p t * Id.t -> 'p t
    | Access_call : Access.t * 'p t * Id.t * 'p t list -> 'p t
    | Method_call : 'p Method_call.t -> 'p t
    | Method_value : 'p Method_value.t -> 'p t
    | Projection : 'p Projection.t -> 'p t
    | Projection_value : GlobRef.t -> 'p t
    | Scope : 'p t * Id.t * 'p Type.t list -> 'p t
    | Type_member : 'p Type.t * Id.t -> 'p t
    | Convertible_to : 'p Type.t -> 'p t
    | Abort : string * 'p Type.t -> 'p t
    | Enum_value : GlobRef.t * Id.t -> 'p t
    | In_place : 'p t
    | In_place_index : int -> 'p t
    | Braced : 'p t list -> 'p t
    | Variant_get : 'p Type.t * 'p t option -> 'p t
    | Holds_alternative : 'p Type.t -> 'p t
    | Declval : 'p Type.t -> 'p t
    | Type_name : 'p Type.t -> 'p t
    | Numeral : GlobRef.t * Numeral.t -> 'p t
    | Foreign_text : string -> 'p t
        (** C++ text from a user-supplied extraction template, whose type
            nothing knows. *)
    | Runtime : Crane_rt.helper -> 'p t
    | Binary : Binary_operator.t * 'p t * 'p t -> 'p t
    | Conditional : 'p t * 'p t * 'p t -> 'p t
    | Unary : Unary_operator.t * 'p t -> 'p t
    | Any_cast : 'p Type.t * 'p t -> 'p t
    | Tolerant_any_cast : 'p Type.t * 'p t -> 'p t
    | Unbox : 'p Unbox.t * 'p t -> 'p t
    | Convert : 'p Type.t * 'p t -> 'p t
    | Erase_callable : 'p Erase_shape.t * 'p t -> 'p t
    | Erased_call : 'p t * 'p t -> 'p t
    | Tolerant_call : 'p t * 'p t list -> 'p t
    | Function_value : 'p t -> 'p t
    | Container_cast : 'p Type.t * 'p t * bool -> 'p t
    | Variant_get_if : 'p Type.t * 'p t -> 'p t
    | Foreign : Foreign.use * 'p Foreign.t -> 'p t
        (** an inline mapping's term template instantiated at one use *)
end =
  Expr

and Binding : sig
  (** Whether an assignment to a variable also declares it. *)
  type 'p t =
    | Declare of 'p Type.t * Core_binder.t option
    | Existing
    | Declare_static of 'p Type.t
end =
  Binding

and Match : sig
  (** The value a {!Stmt.Match} dispatches on. *)
  type 'p scrutinee = {
    expr : 'p Expr.t;
    access : Access.t;
    owned : bool;
        (** the scrutinee is owned (a last use or an explicit move), so its
            payload's fields may be moved out *)
    flat : bool;
        (** a flat single-constructor inductive with no variant wrapper:
            bound directly, with neither [std::get] nor
            [std::holds_alternative] *)
  }

  (** One structured binding of a branch. *)
  type 'p field_binding = {
    name : Id.t;
    type_ : 'p Type.t;
    used : bool;
        (** whether the branch body reads the binding; one it does not is
            written [[[maybe_unused]]] *)
    binder : Core_binder.t option;
  }

  (** A branch of a {!Stmt.Match}. *)
  type 'p branch = {
    ctor_type : 'p Type.t;
    var : Id.t option;
    field_bindings : 'p field_binding list;
    extra_conditions : 'p Expr.t list;
    body : 'p Stmt.t list;
  }
end =
  Match

and Custom_match : sig
  (** How a custom match holds its scrutinee. *)
  type scrutinee_hold =
    | Owned
    | Borrowed

  (** One piece of an instantiated match template. *)
  type piece =
    | Text of string
    | Scrutinee of {parenthesised : bool}
    | Matched_type
    | Type_argument of int
    | Branch of int
    | Binder of int * int
    | Binder_type of int * int

  (** A match template, instantiated or not. *)
  type _ instantiation =
    | Uninstantiated : lowered instantiation
    | Instantiated : piece list -> 'p instantiation

  (** A variable a branch binds. *)
  type 'p param = {
    name : Id.t;
    type_ : 'p Type.t;
    binder : Core_binder.t option;
  }

  type 'p branch = {
    params : 'p param list;
    type_ : 'p Type.t;
    body : 'p Stmt.t list;
  }

  (** A custom match statement. *)
  type 'p t = {
    return_type : 'p Type.t;
    scrutinee : 'p Expr.t;
    type_args : 'p Type.t list;
    branches : 'p branch list;
    template : string;
    inductive : GlobRef.t;
    hold : scrutinee_hold;
    pieces : 'p instantiation;
  }
end =
  Custom_match

and Foreign_block : sig
  (** A multi-statement inline mapping bound to a variable, before its
      template is instantiated. *)
  type 'p t = {
    custom : GlobRef.t;
    template : string;
    result : Id.t;
    result_type : 'p Type.t;
    values : 'p Expr.t list;
    type_args : 'p Type.t list;
    binder : Core_binder.t option;
  }
end =
  Foreign_block

and Stmt : sig
  (** A C++ statement. *)
  type _ t =
    | Return : 'p Expr.t option -> 'p t
    | Declare : Id.t * 'p Type.t * Core_binder.t option -> 'p t
    | Bind_variable : Id.t * 'p Binding.t * 'p Expr.t -> 'p t
    | Expression : 'p Expr.t -> 'p t
    | Custom_match : 'p Custom_match.t -> 'p t
    | Throw : string -> 'p t
    | Switch : {
        scrutinee : 'p Expr.t;
        enum : GlobRef.t;
        branches : (Id.t * 'p t list) list;
        default : 'p t list option;
      }
        -> 'p t
    | Assert : Precondition.t -> 'p t
    | If : {
        condition : 'p Expr.t;
        then_ : 'p t list;
        else_ : 'p t list;
      }
        -> 'p t
    | If_constexpr : {
        test : 'p Type_test.t;
        then_ : 'p t list;
        else_ : 'p t list;
      }
        -> 'p t
    | If_declaration : {
        name : Id.t;
        type_ : 'p Type.t;
        init : 'p Expr.t;
        then_ : 'p t list;
        else_ : 'p t list;
      }
        -> 'p t
    | Foreign_text : string -> 'p t
    | Comment : string -> 'p t
    | Local_struct : Id.t * (Id.t * 'p Type.t) list -> 'p t
    | Local_type_alias : Id.t * 'p Type.t -> 'p t
    | Structured_binding : Id.t list * 'p Expr.t -> 'p t
    | Declare_value_initialized : Id.t * 'p Type.t -> 'p t
    | Assign : 'p Expr.t * 'p Expr.t -> 'p t
    | For_range : Id.t * 'p Expr.t * 'p t list -> 'p t
    | While : 'p Expr.t * 'p t list -> 'p t
    | Block : 'p t list -> 'p t
    | Continue : 'p t
    | Break : 'p t
    | Match : 'p Match.scrutinee * 'p Match.branch list * 'p t list option -> 'p t
    | Foreign_block : lowered Foreign_block.t -> lowered t
        (** instantiated by resolution into the declaration of its result,
            initialised by the mapping's statements *)
end =
  Stmt

and Foreign : sig
  (** What an inline mapping's text does with its arguments. *)
  type shape =
    | Identity
    | Pair_projection of string
    | Other

  (** How an inline mapping's text is printed. *)
  type form =
    | Block  (** a statement block, invoked in place where it is a value *)
    | Bare_callee
    | Templated

  (** An inline mapping's replacement text, classified. *)
  type template = {
    text : string;
    form : form;
    shape : shape;
    linear : bool;
  }

  (** Custom extraction metadata of a mapped global. *)
  type 'p custom = {
    inline : template option;
    custom_yields : 'p Type.t option;
  }

  (** A piece of a [Boxed Element] wrapper. *)
  type wrapper_piece =
    | Wrapper_text of string
    | Wrapper_element

  (** One piece of an instantiated mapping. *)
  type piece =
    | Text of string
    | Type_argument of int
    | Element of int * wrapper_piece list option
    | Value of int
    | Yields
    | Result
    | Statement_end

  (** How a term template is used. *)
  type use =
    | Constant
    | Call
    | Block_value of Written_capture.t
    | Statements

  (** A mapping's text instantiated at one use. *)
  type 'p t = {
    custom : GlobRef.t;
    types : 'p Type.t list;
    values : 'p Expr.t list;
    yields : 'p Type.t option;
    pieces : piece list;
  }
end =
  Foreign

and Value_category : sig
  type t =
    | Mutable_lvalue
    | Const_lvalue
    | Xvalue
    | Prvalue
end =
  Value_category

and Invocation : sig
  (** One way a body invokes a callable parameter: the category of the
      callable and of each argument, at the type the signature gives it. *)
  type 'p t = {
    callable : Value_category.t;
    args : (Value_category.t * 'p Type.t) list;
  }
end =
  Invocation

and Parameter_kind : sig
  (** What kind of template parameter a parameter is. *)
  type _ t =
    | Typename : 'p t
    | Typename_default : 'p Type.t -> 'p t
    | Template : int -> 'p t  (** a template template parameter of this arity *)
    | Callable_declared : lowered Type.t list * lowered Type.t -> lowered t
        (** a callable parameter as its declaration types it, before the
            body that settles its constraint is final *)
    | Invocable : 'p Invocation.t list * 'p Type.t -> 'p t
        (** a callable parameter as the final body invokes it *)
    | Concept : GlobRef.t * 'p Type.t list -> 'p t
end =
  Parameter_kind

and Template : sig
  (** A template parameter list. *)
  type 'p parameters = ('p Parameter_kind.t * Id.t) list
end =
  Template

and Constexpr : sig
  (** Whether a definition may be written [constexpr]. *)
  type _ t =
    | Undecided : lowered t
    | Eligible : 'p t
    | Ineligible : 'p t
end =
  Constexpr

and Visibility : sig
  type t =
    | Public
    | Private
end =
  Visibility

and Section : sig
  (** A BDE section tag grouping struct members. *)
  type t =
    | Types
    | Data
    | Creators
    | Manipulators
    | Accessors
    | Untagged
end =
  Section

and Receiver : sig
  (** Which receivers a method may be called on. *)
  type ref_qualifier =
    | Any
    | Lvalue
    | Rvalue

  (** Whether, and how, a method takes [this]. *)
  type t =
    | Static
    | Instance of {
        this_position : int;
        is_const : bool;
        ref_qualifier : ref_qualifier;
        returns_field : bool;
            (** the method returns one field of its receiver as it is *)
      }
end =
  Receiver

and Method : sig
  (** A member function. *)
  type 'p t = {
    name : Id.t;
    globref : GlobRef.t option;
    type_params : 'p Template.parameters;
    return_type : 'p Type.t;
    params : (Id.t * 'p Type.t) list;
    body : 'p Stmt.t list;
    receiver : Receiver.t;
    is_inline : bool;
    no_pure : bool;
        (** never [constexpr]: a method with a monadic return type performs
            effects even where its erased C++ type looks pure *)
    constexpr : 'p Constexpr.t;
    is_noexcept : bool;
    is_conversion : bool;
        (** a conversion function, written [operator R()] with no return
            type of its own *)
    binders : (Id.t * Core_binder.t) list;
        (** the Core binder each parameter stands for, by the parameter's
            name, where translation bound it for one *)
    receiver_binder : Core_binder.t option;
        (** the Core binder the receiver stands for, where there is one *)
    loop : Control_ir.Loop.t option;
        (** the ControlIR loop the body already is, where it was lowered
            from there; no later pass lowers its control *)
  }
end =
  Method

and Constructor : sig
  (** A constructor. *)
  type 'p t = {
    type_params : 'p Template.parameters;
    params : (Id.t * 'p Type.t) list;
    inits : (Id.t * 'p Expr.t) list;
    body : 'p Stmt.t list;
    explicit : bool;
    noexcept : bool;
  }
end =
  Constructor

and Deferred_struct : sig
  (** A data-only nested struct holding values of the struct it is nested
      in, written as a member template defaulting to its owner. *)
  type 'p t = {
    name : Id.t;
    selves : (Id.t * 'p Type.t) list;
    fields : (Id.t * 'p Type.t) list;
  }
end =
  Deferred_struct

and Out_of_line : sig
  (** A member that can be declared in its struct and defined after it. *)
  type 'p t =
    | Method of 'p Method.t
    | Destructor of 'p Stmt.t list
end =
  Out_of_line

and Field : sig
  (** A struct member. *)
  type 'p t =
    | Data of Id.t * 'p Type.t
    | Entity_data of GlobRef.t * 'p Type.t
        (** a data member named by the global of its record field *)
    | Method of 'p Method.t
    | Constructor of 'p Constructor.t
    | Destructor of 'p Stmt.t list
    | Nested_struct of Id.t * 'p member list
    | Deferred_struct of 'p Deferred_struct.t
    | Nested_type_alias of 'p Template.parameters * Id.t * 'p Type.t
    | Out_of_line_declaration of 'p Out_of_line.t
    | Deleted_default_constructor
    | Defaulted_special_members

  (** A member with its visibility and section. *)
  and 'p member = 'p t * Visibility.t * Section.t
end =
  Field

and Namespace : sig
  (** The struct an inductive at namespace scope is wrapped in, and whether
      it is written as one struct with the struct it holds. *)
  type wrapper = {
    ref_ : GlobRef.t;
    merges : bool;
  }
end =
  Namespace

and Struct : sig
  (** A struct: its members, and what the [struct] line says. *)
  type 'p t = {
    ref_ : GlobRef.t;
    fields : 'p Field.member list;
    type_params : 'p Template.parameters;
    constraint_ : 'p Expr.t option;
    needs_shared_from_this : bool;
        (** inherit [enable_shared_from_this], as a method returns [this] *)
  }
end =
  Struct

and Member_definition : sig
  (** A member defined outside the struct that declares it; [type_params]
      are the struct's. *)
  type 'p t = {
    owner : GlobRef.t;
    enclosing : Namespace.wrapper option;
    type_params : 'p Template.parameters;
    member : 'p Out_of_line.t;
  }
end =
  Member_definition

and Type_alias : sig
  (** A type alias, possibly naming a type without defining it. *)
  type 'p t = {
    type_params : 'p Template.parameters;
    name : GlobRef.t;
    rhs : 'p Type.t option;
    note : string option;
  }
end =
  Type_alias

and Variable : sig
  (** A global variable and its initialiser. *)
  type 'p t = {
    ref_ : GlobRef.t;
    type_ : 'p Type.t;
    init : 'p Expr.t;
    constexpr : 'p Constexpr.t;
  }
end =
  Variable

and Function : sig
  (** The qualified name a function is written under: never empty. *)
  type 'p path = {
    outer : GlobRef.t * 'p Type.t list;
    inner : (GlobRef.t * 'p Type.t list) list;
  }

  (** A definition names every parameter and has a body; a declaration may
      leave a parameter anonymous. *)
  type 'p shape =
    | Definition of (Id.t * 'p Type.t) list * 'p Stmt.t list
    | Declaration of (Id.t option * 'p Type.t) list

  (** A function declaration or definition. *)
  type 'p t = {
    path : 'p path;
    return_type : 'p Type.t;
    no_pure : bool;
        (** never [constexpr]: monadic functions and axiom stubs are not *)
    constexpr : 'p Constexpr.t;
    shape : 'p shape;
    binders : (Id.t * Core_binder.t) list;
        (** the Core binder each parameter stands for, by the parameter's
            name, where translation bound it for one *)
    loop : Control_ir.Loop.t option;
        (** the ControlIR loop the body already is, where it was lowered
            from there; no later pass lowers its control *)
  }
end =
  Function

and Enum : sig
  (** An enum class. *)
  type 'p t = {
    ref_ : GlobRef.t;
    ctors : Id.t list;
    rocq_names : string list;  (** for the doc comments *)
    type_params : 'p Template.parameters;
  }
end =
  Enum

and Decl : sig
  (** A declaration. *)
  type 'p t =
    | Template of 'p Template.parameters * 'p Expr.t option * 'p t
    | Namespace of Namespace.wrapper option * 'p t list
    | Function of 'p Function.t
    | Struct of 'p Struct.t
    | Variable of 'p Variable.t
    | Concept of GlobRef.t * 'p Expr.t
    | Static_assert of 'p Expr.t * string option
    | Type_alias of 'p Type_alias.t
    | Struct_forward_declaration of 'p Template.parameters * GlobRef.t
    | Merged_struct_members of 'p Struct.t
        (** the members a promoted inductive contributes to the struct it
            was merged into *)
    | Member_definition of 'p Member_definition.t
    | Enum of 'p Enum.t
end =
  Decl

and Inductive_kind : sig
  (** How an inductive is written in C++. *)
  type t =
    | Sum  (** a [std::variant] of its constructors *)
    | Enum  (** an enum class *)
    | Record of GlobRef.t option list
    | Eponymous_record of GlobRef.t option list
        (** a record merged into its module's struct *)
    | Type_class of GlobRef.t option list  (** a concept *)
end =
  Inductive_kind
