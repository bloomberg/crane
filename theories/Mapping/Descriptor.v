(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mapping descriptors (docs/typed-mappings-design.md).

    The data a typed mapping is written in: inductive types and records only,
    no helper functions.  A mapping is an instance of [TypeMapping T] for a
    source type, or of [OperationMapping (Ref source)] for a source operation;
    importing the file that exports an instance selects it.

    Names.  The structured C++ type grammar lives in the nested module
    [Crane.Cpp], so its constructors are written as in the design:
    [Crane.Cpp.Name], [Crane.Cpp.Apply], [Crane.Cpp.SourceType],
    [Crane.Cpp.StoredComponent], [Crane.Cpp.Pointer], [Crane.Cpp.Const],
    [Crane.Cpp.UnsafeVerbatim], [Crane.Cpp.TypeArg], [Crane.Cpp.ValueArg]
    (fully qualified: [Crane.Mapping.Descriptor.Crane.Cpp.Name], ...).
    Everything else is at the top level of this file, under the design's
    names.

    Every string is a [PrimString.string]; a mapping file opens
    [pstring_scope] to write string literals inside lists.

    Implicit arguments.  [ReadViews], [ReadWriteViews], [MaterialiseView]
    and [BorrowOnly] take the mapped type implicitly; [NoViews] takes it
    explicitly, as in [NoViews Example]. *)
From Corelib Require Import PrimString.

(** A Rocq declaration by identity.  The plugin keeps the argument of [Ref]
    as a reference and never unfolds it. *)
Inductive Declaration : Type :=
| Ref : forall {T : Type}, T -> Declaration.

Module Crane.
Module Cpp.

(** A structured C++ type: pointers and const qualification are nodes, so
    they print with correct declarator binding. *)
Inductive TypeExpr : Type :=
| Name (qualified_name : string)
| Apply (qualified_name : string) (arguments : list TypeArgument)
| SourceType (T : Type)
| StoredComponent (name : string)
| Pointer (pointee : TypeExpr)
| Const (inner : TypeExpr)
| UnsafeVerbatim (cpp : string)

with TypeArgument : Type :=
| TypeArg (type_argument : TypeExpr)
| ValueArg (value_argument : string).

End Cpp.
End Crane.

(** How a value is created: an expression, or an initialiser of the owning
    [%result] slot followed by a body. *)
Inductive Construction : Type :=
| Expr (cpp : string)
| WithBody (initialiser body : string).

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

(** The plugin finds these inductives by the names below and reads
    constructors by their position, so the constructor order above is part of
    its interface. *)
Register Declaration as crane.mapping.Declaration.
Register Crane.Cpp.TypeExpr as crane.mapping.TypeExpr.
Register Crane.Cpp.TypeArgument as crane.mapping.TypeArgument.
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
