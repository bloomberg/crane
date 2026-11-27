(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mapping descriptors (documented in the Reference Manual, Typed
    mappings).

    The data a typed mapping is written in: inductive types and records.  A
    mapping is an instance of [TypeMapping T] for a source type, or of
    [OperationMapping (Ref source)] for a source operation; importing the
    file that exports an instance selects it.  The plugin reads a descriptor
    after reducing it, so a descriptor may be computed by Rocq functions
    ([Crane.Mapping.Cpp] has a few for operation bodies).

    Names.  The structured C++ type grammar lives in the nested module
    [Crane.Cpp], so its constructors carry that prefix:
    [Crane.Cpp.Name], [Crane.Cpp.Apply], [Crane.Cpp.SourceType],
    [Crane.Cpp.StoredComponent], [Crane.Cpp.Pointer], [Crane.Cpp.Const],
    [Crane.Cpp.UnsafeVerbatim], [Crane.Cpp.TypeArg], [Crane.Cpp.ValueArg]
    (fully qualified: [Crane.Mapping.Descriptor.Crane.Cpp.Name], ...), and so
    does the grammar of an operation's body, [Crane.Cpp.Term]; a mapping file
    may [Import Crane.Cpp] to write them unqualified.  Everything else is at
    the top level of this file.

    Operation bodies.  An operation's C++ is a [Crane.Cpp.Term] (the
    [Structured] construction) wherever the grammar can say it, so that Crane
    sees the arithmetic and conversions in it: it folds a conversion of a
    literal into a literal of the target type, drops a conversion to the type
    the operand already has, and drops an [Exact] conversion to a type wide
    enough for the operand under another conversion.  [Expr] text is the
    escape hatch for what the grammar does not cover (statements, loops,
    lambdas).  An integer literal is a [Z] of an [IntType], in its range.

    Every string is a [PrimString.string]; a mapping file opens
    [pstring_scope] to write string literals inside lists.

    Implicit arguments.  [ReadViews], [ReadWriteViews], [MaterialiseView]
    and [BorrowOnly] take the mapped type implicitly; [NoViews] takes it
    explicitly, as in [NoViews Example]. *)
From Corelib Require Import PrimString BinNums.

(** A Rocq declaration by identity.  The plugin keeps the argument of [Ref]
    as a reference and never unfolds it. *)
Inductive Declaration : Type :=
| Ref : forall {T : Type}, T -> Declaration.

Module Crane.
Module Cpp.

(** The C++ integer types: [int8_t] ... [uint64_t], [std::size_t], [char],
    [unsigned char].  [Size] and [U64] are distinct types (they are on
    macOS), and [Char]'s signedness is the platform's. *)
Inductive IntType : Type :=
| I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64 | Size | Char | UChar.

(** A structured C++ type: pointers and const qualification are nodes, so
    they print with correct declarator binding.  [Int], [Bool] and
    [Float64] are the built-in types; a canonical type written [Int] lets
    Crane know an operation's argument is that integer type.  [SourceType T]
    is the C++ type Crane chooses for the mapped type's parameter [T] (a
    type, or a type family such as an event family).  [ResultType]
    is the type a use of an operation yields, and [TypeParameter x] the
    type an operation's type parameter [x] is instantiated at (both only in
    an operation's body).  [BoxedComponent c box], in a canonical type, is
    the component [c], or [box] (naming the element [StoredComponent c])
    where the element is an inductive recursive through the mapped type:
    a container C++ needs its element complete to name ([immer] containers)
    holds such an element boxed.  A constructor's [%stored(c)] is boxed the
    same way; a view's and a projection's are not. *)
Inductive TypeExpr : Type :=
| Name (qualified_name : string)
| Apply (qualified_name : string) (arguments : list TypeArgument)
| SourceType {K : Type} (T : K)
| StoredComponent (name : string)
| Pointer (pointee : TypeExpr)
| Const (inner : TypeExpr)
| UnsafeVerbatim (cpp : string)
| Int (t : IntType)
| Bool
| Float64
| ResultType
| TypeParameter (name : string)
| BoxedComponent (name : string) (box : TypeExpr)

with TypeArgument : Type :=
| TypeArg (type_argument : TypeExpr)
| ValueArg (value_argument : string).

(** How a value is converted to an integer type: [Exact] asserts the value
    is preserved (the mapping's claim, not checked); [Wrap] reduces it
    modulo two to the target's width, as C++ converts an integer;
    [Saturate] clamps it to the target's range ([std::saturate_cast]);
    [ToEnum] converts to an enumeration. *)
Inductive Conversion : Type :=
| Exact | Wrap | Saturate | ToEnum.

(** What an arithmetic operator does on overflow: what C++ does
    ([Unchecked]), wrap modulo two to the width, or saturate
    ([std::add_sat] ...). *)
Inductive Overflow : Type :=
| Unchecked | Wrapping | Saturating.

Inductive BinOp : Type :=
| Add (overflow : Overflow)
| Sub (overflow : Overflow)
| Mul (overflow : Overflow)
| Div | Mod
| Less | LessEq | Greater | GreaterEq | Equal | NotEqual
| And | Or
| BitAnd | BitOr | BitXor | Shl | Shr.

Inductive UnOp : Type :=
| Negate | Not | BitNot.

(** An operation's C++ body.  [Arg x] is the contract's argument [x], each
    evaluated once however often the body names it; [LetIn x v b] names [v]
    as [Var x] in [b] (by substitution: [v] is written at each use).
    [Call f ts args] is [f<ts>(args)], [Method e m args] is [e.m(args)],
    [Build t args] is [t(args)], [EnumValue t c] is [t::c].  [Verbatim] is
    C++ text naming no argument. *)
Inductive Term : Type :=
| Arg (name : string)
| IntLit (t : IntType) (value : Z)
| BoolLit (value : bool)
| StringLit (value : string)
| Unop (op : UnOp) (operand : Term)
| Binop (op : BinOp) (lhs rhs : Term)
| Cond (condition then_ else_ : Term)
| Convert (how : Conversion) (target : TypeExpr) (operand : Term)
| Call (callee : string) (type_arguments : list TypeExpr) (arguments : list Term)
| Method (receiver : Term) (name : string) (arguments : list Term)
| Member (object : Term) (field : string)
| Index (object index : Term)
| Build (type_ : TypeExpr) (arguments : list Term)
| EnumValue (type_ : TypeExpr) (name : string)
| LetIn (name : string) (value body : Term)
| Var (name : string)
| Verbatim (cpp : string).

End Cpp.
End Crane.

(** How a value is created: an expression, or an initialiser of the owning
    [%result] slot followed by a body; for an operation, a structured body. *)
Inductive Construction : Type :=
| Expr (cpp : string)
| WithBody (initialiser body : string)
| Structured (body : Crane.Cpp.Term).

Inductive CopyModel : Type :=
| BitCopy
| RetainIdentity
| DuplicateValue
| CopyComponents (components : list string)
| UnknownCopy.

Inductive ReadStyle : Type :=
| ReadByValue
| ReadByConstReference
| ReadByComponents (components : list string).

Inductive HandlePass : Type :=
| HandleByValue
| HandleByConstReference.

Inductive PhysicalParameter : Type :=
| CanonicalByValue
| CanonicalByConstReference
| CanonicalByMutableReference
| ExactParameter (cpp : string).

Record ExplicitAccessSpec : Type := {
  explicit_read : PhysicalParameter;
  explicit_write : option PhysicalParameter;
  explicit_replace : option PhysicalParameter
}.

Inductive AccessModel : Type :=
| ReadOnlyValue (read_style : ReadStyle)
| MutableValue (read_style : ReadStyle)
| ReadOnlyHandle (handle_pass : HandlePass)
| MutableHandle (handle_pass : HandlePass)
| ExplicitAccess (specification : ExplicitAccessSpec).

Inductive ValueModel : Type :=
| Structural
| Identity
| Unspecified.

Inductive LifetimeModel : Type :=
| NativeRAII
| RegionOwned (region : Declaration)
| ExternallyOwned
| ManualShared (retain : Declaration) (release : Declaration).

Inductive ReleasePlan : Type :=
| OrdinaryRelease
| DrainWith (cpp : string).

Inductive ViewMode : Type :=
| ReadOnlyView
| WritableView.

Inductive ViewEscape (T : Type) : Type :=
| MaterialiseView (construction : Construction)
| BorrowOnly.
Arguments MaterialiseView {T} construction.
Arguments BorrowOnly {T}.

(** The read view of a type with literals (a string) is constructible from
    a C++ string literal, and from a literal and its length: a literal
    taken as the view is the view of the literal itself. *)
Record ViewSpec (T : Type) (mode : ViewMode) : Type := {
  view_headers : list string;
  view_cpp : Crane.Cpp.TypeExpr;
  (** [%value] is a live canonical lvalue or handle. *)
  view_from_canonical : string;
  view_escape : ViewEscape T
}.

(** No view, one read view, or a read view and a writable view with the
    conversion narrowing the second to the first. *)
Inductive Views (T : Type) : Type :=
| NoViews
| ReadViews
    (read_view : ViewSpec T ReadOnlyView)
| ReadWriteViews
    (read_view : ViewSpec T ReadOnlyView)
    (write_view : ViewSpec T WritableView)
    (read_from_write : string).
Arguments ReadViews {T} read_view.
Arguments ReadWriteViews {T} read_view write_view read_from_write.

Inductive ComponentType : Type :=
| KnownType (T : Type)
| FieldType (constructor : Declaration) (field : nat).

Record Component : Type := {
  component_name : string;
  component_type : ComponentType
}.

Inductive Projection : Type :=
| OwnedProjection (cpp : string)
| CanonicalBorrowProjection (cpp : string)
| ReadViewProjection (cpp : string).

Inductive ObservationRequirement : Type :=
| PreferredObservation
| CanonicalObservation.

Record ConstructorView : Type := {
  view_requirement : ObservationRequirement;
  case_test : string;
  case_fields : list (nat * Projection)
}.

Record ConstructorMapping : Type := {
  ctor_source : Declaration;
  ctor_build : Construction;
  ctor_view : option ConstructorView
}.

(** A match tests the constructor views in the order [AlgebraicInterface]
    lists them, and the last one listed needs no test: a view's test may
    assume the views listed before it failed. *)
Inductive TypeInterface : Type :=
| AbstractInterface
| AlgebraicInterface (constructors : list ConstructorMapping).

Inductive NumeralAction : Type :=
| NumeralZero
| NumeralOne
| NumeralSuccessor (field : nat)
| NumeralDouble (field : nat)
| NumeralDoublePlusOne (field : nat)
| NumeralIdentity (field : nat)
| NumeralNegate (field : nat).

Record NumeralCase : Type := {
  numeral_constructor : Declaration;
  numeral_action : NumeralAction
}.

Inductive NumeralEmitter : Type :=
| IntegerToken (prefix suffix : string)
| DecimalConstructor (callee : string).

Record NumeralSpec (T : Type) : Type := {
  numeral_cases : list NumeralCase;
  numeral_emitter : NumeralEmitter;
  numeral_converters : list Declaration
}.

(** The mapping of a source type. *)
Class TypeMapping (T : Type) : Type := {
  type_headers : list string;
  type_cpp : Crane.Cpp.TypeExpr;

  type_components : list Component;
  type_copy : CopyModel;
  type_access : AccessModel;
  type_views : Views T;

  type_interface : TypeInterface;
  type_model : ValueModel;
  type_lifetime : LifetimeModel;
  type_release : ReleasePlan;

  type_numerals : option (NumeralSpec T)
}.

Inductive InputUse : Type :=
| Ignore
| Read
| ReadCanonical
| Write
| WriteCanonical
| Take
| Replace
| OpaqueUse.

Record ArgumentSpec : Type := {
  argument_name : string;
  argument_use : InputUse
}.

Record ComponentPath : Type := {
  path_argument : string;
  path_components : list string
}.

Inductive InitialMultiplicity : Type :=
| InitialiseOnce
| InitialiseMany.

Record ComponentInitialiser : Type := {
  initial_component : string;
  initial_source_argument : option string;
  initial_multiplicity : InitialMultiplicity
}.

Inductive BorrowForm : Type :=
| CanonicalBorrow
| ReadViewBorrow
| WritableViewBorrow.

Inductive ResultSpec : Type :=
| ReturnValue
| ReturnBorrowed
    (form : BorrowForm)
    (origin : ComponentPath)
| ReturnSameIdentity
    (argument : string)
| ReturnFreshIdentity
    (initialisers : list ComponentInitialiser)
| ReturnOpaque.

Inductive OperationFact : Type :=
| ReadsComponent (target : ComponentPath)
| WritesComponent (target : ComponentPath) (source_argument : option string)
| InvalidatesElementBorrows (target : ComponentPath)
| InvalidatesViews (target : ComponentPath)
| RetainsArgument (argument : string) (destination : ComponentPath)
| ReleasesIdentity (argument : string)
| ExternalEffect (name : string).

Inductive OperationContract : Type :=
| PureOperation
    (arguments : list ArgumentSpec) (result : ResultSpec) (facts : list OperationFact)
| EffectfulOperation
    (arguments : list ArgumentSpec) (result : ResultSpec) (facts : list OperationFact)
| OpaqueOperation.

(** The mapping of a source operation, named by [Ref]. *)
Class OperationMapping (source : Declaration) : Type := {
  operation_headers : list string;
  operation_cpp : Construction;
  operation_contract : OperationContract
}.

(** A mapped identity type whose value may live in a local variable
    instead of its canonical owner, where it does not escape the function
    that creates it: every use is a view, none is stored, returned, passed
    as the canonical value or named under a closure.  The local holds the
    type's one component by value, initialised from the argument its
    [ReturnFreshIdentity] operation initialises the component from once;
    [local_view] spells either view of the local, [%value] being the local
    lvalue.  [local_tag] is unused; it keeps the class a record. *)
Class LocalStorage (T : Type) : Type := {
  local_view : string;
  local_tag : unit
}.

(** The plugin finds these inductives by the names below and reads
    constructors by their position, so the constructor order above is part of
    its interface. *)
Register Declaration as crane.mapping.Declaration.
Register Crane.Cpp.TypeExpr as crane.mapping.TypeExpr.
Register Crane.Cpp.TypeArgument as crane.mapping.TypeArgument.
Register Crane.Cpp.IntType as crane.mapping.IntType.
Register Crane.Cpp.Conversion as crane.mapping.Conversion.
Register Crane.Cpp.Overflow as crane.mapping.Overflow.
Register Crane.Cpp.BinOp as crane.mapping.BinOp.
Register Crane.Cpp.UnOp as crane.mapping.UnOp.
Register Crane.Cpp.Term as crane.mapping.Term.
Register Construction as crane.mapping.Construction.
Register CopyModel as crane.mapping.CopyModel.
Register ReadStyle as crane.mapping.ReadStyle.
Register HandlePass as crane.mapping.HandlePass.
Register PhysicalParameter as crane.mapping.PhysicalParameter.
Register ExplicitAccessSpec as crane.mapping.ExplicitAccessSpec.
Register AccessModel as crane.mapping.AccessModel.
Register ValueModel as crane.mapping.ValueModel.
Register LifetimeModel as crane.mapping.LifetimeModel.
Register ReleasePlan as crane.mapping.ReleasePlan.
Register ViewMode as crane.mapping.ViewMode.
Register ViewEscape as crane.mapping.ViewEscape.
Register ViewSpec as crane.mapping.ViewSpec.
Register Views as crane.mapping.Views.
Register ComponentType as crane.mapping.ComponentType.
Register Component as crane.mapping.Component.
Register Projection as crane.mapping.Projection.
Register ObservationRequirement as crane.mapping.ObservationRequirement.
Register ConstructorView as crane.mapping.ConstructorView.
Register ConstructorMapping as crane.mapping.ConstructorMapping.
Register TypeInterface as crane.mapping.TypeInterface.
Register NumeralAction as crane.mapping.NumeralAction.
Register NumeralCase as crane.mapping.NumeralCase.
Register NumeralEmitter as crane.mapping.NumeralEmitter.
Register NumeralSpec as crane.mapping.NumeralSpec.
Register TypeMapping as crane.mapping.TypeMapping.
Register LocalStorage as crane.mapping.LocalStorage.
Register InputUse as crane.mapping.InputUse.
Register ArgumentSpec as crane.mapping.ArgumentSpec.
Register ComponentPath as crane.mapping.ComponentPath.
Register InitialMultiplicity as crane.mapping.InitialMultiplicity.
Register ComponentInitialiser as crane.mapping.ComponentInitialiser.
Register BorrowForm as crane.mapping.BorrowForm.
Register ResultSpec as crane.mapping.ResultSpec.
Register OperationFact as crane.mapping.OperationFact.
Register OperationContract as crane.mapping.OperationContract.
Register OperationMapping as crane.mapping.OperationMapping.
