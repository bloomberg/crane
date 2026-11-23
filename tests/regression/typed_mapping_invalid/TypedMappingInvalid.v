(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Invalid typed mapping descriptors (design 19, 24.12).  Each module
    declares one invalid instance and checks that resolving it fails with a
    focused diagnostic; the instance is active only inside its module.  The
    checks run while TypedMappingInvalid.vo is built; the extraction at the
    end does not use the mappings. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.

Inductive Shape : Type := circle (radius : nat) | square (side : nat).
Inductive Other : Type := other.

Axiom Text : Type.
Axiom MutableText : Type.
Axiom ViewText : Type.

Axiom text_op : forall (text : Text) (count : nat), Text.
Axiom mutable_op : forall (text : MutableText) (count : nat), MutableText.
Axiom view_op : forall (text : ViewText), ViewText.

(** Component names are unique. *)
Module DuplicateComponent.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [{| component_name := "size"; component_type := KnownType nat |};
          {| component_name := "size"; component_type := KnownType nat |}];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "component ""size"" is declared more than once".
End DuplicateComponent.

(** Every component a copy model names is declared. *)
Module UnknownComponent.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := CopyComponents ["missing"];
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "CopyComponents names component ""missing"", which is not declared in type_components".
End UnknownComponent.

(** Every component a read style names is declared. *)
Module UnknownReadComponent.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue (ReadByComponents ["missing"]);
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "ReadByComponents names component ""missing"", which is not declared in type_components".
End UnknownReadComponent.

(** The canonical type names declared components only. *)
Module UnknownCanonicalComponent.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "type_cpp names component ""element"", which is not declared in type_components".
End UnknownCanonicalComponent.

(** A view type names declared components only. *)
Module ViewUnknownComponent.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := ReadViews
         {| view_headers := [];
            view_cpp := Crane.Cpp.Apply "std::span" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
            view_from_canonical := "%value";
            view_escape := BorrowOnly |};
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "read view_cpp names component ""element"", which is not declared in type_components".
End ViewUnknownComponent.

(** A writable view needs a mutable access model. *)
Module WritableViewReadOnly.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := ReadWriteViews
         {| view_headers := [];
            view_cpp := Crane.Cpp.Name "shape_view";
            view_from_canonical := "%value";
            view_escape := BorrowOnly |}
         {| view_headers := [];
            view_cpp := Crane.Cpp.Name "shape_mut_view";
            view_from_canonical := "%value";
            view_escape := BorrowOnly |}
         "%view";
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "ReadWriteViews declares a writable view, but the access model is read-only".
End WritableViewReadOnly.

(** A raw pointer owns nothing, so it cannot be NativeRAII. *)
Module RawPointerNativeRAII.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Name "shape");
       type_components := [];
       type_copy := BitCopy;
       type_access := MutableHandle HandleByValue;
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Identity;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "the canonical type is a raw pointer, which owns nothing, but the lifetime model is NativeRAII".
End RawPointerNativeRAII.

(** A canonical type is a value type, never a reference. *)
Module CanonicalReference.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.UnsafeVerbatim "shape&";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "the canonical type is a C++ reference".
End CanonicalReference.

(** Constructor mappings name constructors of the mapped type. *)
Module ConstructorWrongFamily.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AlgebraicInterface [{| ctor_source := Ref other; ctor_build := Expr "shape{}"; ctor_view := None |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "AlgebraicInterface names Ref other, which is not a constructor of the mapped type".
End ConstructorWrongFamily.

(** Each constructor is mapped at most once. *)
Module ConstructorTwice.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AlgebraicInterface [{| ctor_source := Ref circle; ctor_build := Expr "shape{}"; ctor_view := None |}; {| ctor_source := Ref circle; ctor_build := Expr "shape{}"; ctor_view := None |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "Ref circle appears more than once in AlgebraicInterface".
End ConstructorTwice.

(** Projection field positions exist (from 0, after the parameters). *)
Module ConstructorFieldPosition.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AlgebraicInterface [{| ctor_source := Ref circle; ctor_build := Expr "shape{}"; ctor_view := Some {| view_requirement := PreferredObservation; case_test := "%scrut.is_circle()"; case_fields := [(1, OwnedProjection "%scrut.radius()")] |} |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "names field 1, but the constructor has 1 field (numbered from 0)".
End ConstructorFieldPosition.

(** A constructor test sees only its own holes. *)
Module TypeTemplateHole.
  #[export] Instance bad : TypeMapping Shape :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Shape;
       type_interface := AlgebraicInterface [{| ctor_source := Ref circle; ctor_build := Expr "shape{}"; ctor_view := Some {| view_requirement := PreferredObservation; case_test := "%arg(x)"; case_fields := [] |} |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Shape Fails With
    "case_test uses the template hole %arg(x), which is not available there".
End TypeTemplateHole.

(** Every instance parameter is determined by the mapped type. *)
Module UnconstrainedParameter.
  #[export] Instance bad (n : nat) : TypeMapping Other :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "shape";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Other;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Other Fails With
    "The type mapping bad for Other leaves some of its parameters undetermined".
End UnconstrainedParameter.

(** Mappings for the operation tests: [Text] is a read-only value without
    views, [MutableText] a mutable handle with a [contents] component,
    [ViewText] a read-only value with a read view. *)
Module TextMappings.
  #[export] Instance text_mapping : TypeMapping Text :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "std::string";
       type_components := [];
       type_copy := DuplicateValue;
       type_access := ReadOnlyValue ReadByConstReference;
       type_views := NoViews Text;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  #[export] Instance mutable_text_mapping : TypeMapping MutableText :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Apply "std::shared_ptr" [Crane.Cpp.TypeArg (Crane.Cpp.Name "std::string")];
       type_components := [{| component_name := "contents"; component_type := KnownType nat |}];
       type_copy := RetainIdentity;
       type_access := MutableHandle HandleByConstReference;
       type_views := NoViews MutableText;
       type_interface := AbstractInterface;
       type_model := Identity;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  #[export] Instance view_text_mapping : TypeMapping ViewText :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "std::string";
       type_components := [];
       type_copy := DuplicateValue;
       type_access := ReadOnlyValue ReadByConstReference;
       type_views := ReadViews
         {| view_headers := [];
            view_cpp := Crane.Cpp.Name "std::string_view";
            view_from_canonical := "std::string_view{%value}";
            view_escape := MaterialiseView (Expr "std::string{%view}") |};
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
End TextMappings.

Module ValidOperations.
  Import TextMappings.
  Crane Check Mapping Text Selects text_mapping.
  Crane Check Mapping MutableText Selects mutable_text_mapping.
  Crane Check Mapping ViewText Selects view_text_mapping.
End ValidOperations.

(** Write needs a mutable type. *)
Module WriteReadOnly.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Write |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "argument ""text"" is written, but its type's access model is read-only".
End WriteReadOnly.

(** WriteCanonical needs a mutable type. *)
Module WriteCanonicalReadOnly.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := WriteCanonical |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "argument ""text"" is written, but its type's access model is read-only".
End WriteCanonicalReadOnly.

(** Replace needs replace capability. *)
Module ReplaceReadOnly.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Replace |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "argument ""text"" is replaced, but its type's access model is read-only".
End ReplaceReadOnly.

(** A pure operation writes nothing. *)
Module PureWrite.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref mutable_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Write |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping mutable_op Fails With
    "a PureOperation cannot write argument ""text""".
End PureWrite.

(** A pure operation creates no fresh identity. *)
Module PureFreshIdentity.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref mutable_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           (ReturnFreshIdentity [])
           [] |}.
  Crane Check Mapping mutable_op Fails With
    "a PureOperation cannot return a fresh identity".
End PureFreshIdentity.

(** A pure operation has no external effect. *)
Module PureExternalEffect.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref mutable_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [ExternalEffect "io"] |}.
  Crane Check Mapping mutable_op Fails With
    "a PureOperation cannot have an external effect (ExternalEffect)".
End PureExternalEffect.

(** A read-view borrow needs a read view on the result type. *)
Module ReadViewBorrowNoView.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           (ReturnBorrowed ReadViewBorrow {| path_argument := "text"; path_components := [] |})
           [] |}.
  Crane Check Mapping text_op Fails With
    "the result is a ReadViewBorrow, but the result type declares no read view".
End ReadViewBorrowNoView.

(** A writable-view borrow needs a writable view on the result type. *)
Module WritableViewBorrowNoView.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref view_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Read |}]
           (ReturnBorrowed WritableViewBorrow {| path_argument := "text"; path_components := [] |})
           [] |}.
  Crane Check Mapping view_op Fails With
    "the result is a WritableViewBorrow, but the result type declares no writable view".
End WritableViewBorrowNoView.

(** A borrowed result names its owner. *)
Module BorrowNoOwner.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         PureOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           (ReturnBorrowed CanonicalBorrow {| path_argument := ""; path_components := [] |})
           [] |}.
  Crane Check Mapping text_op Fails With
    "the borrowed result's origin has no owner argument".
End BorrowNoOwner.

(** Fact targets name components of the argument's type. *)
Module InvalidatesUnknownComponent.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref mutable_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := WriteCanonical |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [InvalidatesViews {| path_argument := "text"; path_components := ["nothing"] |}] |}.
  Crane Check Mapping mutable_op Fails With
    "InvalidatesViews names component ""nothing"", which the type of argument ""text"" does not declare".
End InvalidatesUnknownComponent.

(** Fact targets name declared arguments. *)
Module WritesUnknownArgument.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref mutable_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Write |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [WritesComponent {| path_argument := "text"; path_components := ["contents"] |} (Some "value")] |}.
  Crane Check Mapping mutable_op Fails With
    "WritesComponent names argument ""value"", which is not declared in the contract".
End WritesUnknownArgument.

(** An Ignore argument does not appear in the template. *)
Module IgnoredArgumentReferenced.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text), %arg(count))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Ignore |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "operation_cpp refers to %arg(count), but the argument is declared Ignore".
End IgnoredArgumentReferenced.

(** Every %arg hole names a declared argument. *)
Module UndeclaredArgument.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(size))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "operation_cpp names argument ""size"", which is not declared in the contract".
End UndeclaredArgument.

(** An operation template sees only operation holes. *)
Module UnavailableHole.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%scrut)";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "count"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "operation_cpp uses the template hole %scrut, which is not available in an operation template".
End UnavailableHole.

(** Argument names are unique. *)
Module DuplicateArgument.
  Import TextMappings.
  #[export] Instance bad : OperationMapping (Ref text_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "f(%arg(text))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "text"; argument_use := Read |}; {| argument_name := "text"; argument_use := Read |}]
           ReturnValue
           [] |}.
  Crane Check Mapping text_op Fails With
    "argument ""text"" is declared more than once".
End DuplicateArgument.

(** [UnsafeVerbatim] is accepted with the warning [crane-mapping-unsafe]. *)
Module UnsafeVerbatimWarns.
  #[export] Instance legacy : TypeMapping Other :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.UnsafeVerbatim "legacy::other";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Other;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
  Crane Check Mapping Other Selects legacy.
End UnsafeVerbatimWarns.

(** [Ref] names a declaration; a term that is not a reference is rejected
    when the instances are enumerated. *)
Module RefNotReference.
  #[export] Instance bad : OperationMapping (Ref (fun n : nat => n)) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(n)";
       operation_contract := OpaqueOperation |}.
  Crane Check Mapping text_op Fails With
    "does not name its operation by a reference".
End RefNotReference.

Module Sample.
  Definition answer : nat := 42.
End Sample.

Crane Extraction "typed_mapping_invalid" Sample.
