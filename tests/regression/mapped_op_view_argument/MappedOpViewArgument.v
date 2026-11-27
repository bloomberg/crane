(** Found by Ephyra round 24 (whose generator writes its own typed
    mappings). Under [Mapping.Std] a primitive-string parameter that is
    only read is taken as [std::string_view].  Passed as an operation
    mapping's argument typed by a type variable, which the template is
    given canonically and returns, the view went into the template as it
    was, so the template's result was a [std::string_view] (or did not
    type at all) where the declaration returns [std::string].

    - [deque_fold]: [Mapping.DequeList]'s [fold_left] with the parameter as
      the initial accumulator: [auto _a] was a [std::string_view], which the
      step [[](std::string a, uint64_t) { return a; }] cannot take.
    - [maybe_get]: a test-local [OperationMapping] of
      [mb_get : maybe A -> A -> A] as [_m.has_value() ? *_m : _d]: the
      conditional's type was [std::string_view] ("no viable conversion from
      returned value of type 'std::string_view' to function return type
      'std::string'").

    Fixed: the access analysis counted a [Read] argument as one a view may
    be passed to whatever its binder's type; one the template is given no
    view of (its binder typed by a type variable) needs the canonical
    representation, so the parameter is now a [const std::string &]
    ([Core_plan.Access.read_off]).

    Expected: compiles; [result = 6]. *)
From Crane Require Import Mapping.NatInt Mapping.Std Mapping.DequeList.
From Corelib Require Import PrimString.
From Crane Require Import Extraction Mapping.Descriptor.
From Stdlib Require Import List Uint63 BinInt.
Import ListNotations.

Inductive maybe (A : Type) : Type := Nothing | Just (x : A).
Arguments Nothing {A}.
Arguments Just {A} x.

Definition mb_get {A : Type} (m : maybe A) (d : A) : A :=
  match m with Nothing => d | Just x => x end.

Module Mappings.
Local Open Scope pstring_scope.

#[export] Instance maybe_mapping (A : Type) : TypeMapping (maybe A) :=
  {| type_headers := ["optional"];
     type_cpp := Crane.Cpp.Apply "std::optional" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components := [{| component_name := "element"; component_type := FieldType (Ref (@Just A)) 0 |}];
     type_copy := CopyComponents ["element"];
     type_access := ReadOnlyValue (ReadByComponents ["element"]);
     type_views := NoViews (maybe A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@Nothing A);
             ctor_build := Expr "std::optional<%stored(element)>{}";
             ctor_view := Some {| view_requirement := CanonicalObservation;
                                  case_test := "!%scrut.has_value()"; case_fields := [] |} |};
          {| ctor_source := Ref (@Just A);
             ctor_build := Expr "std::optional<%stored(element)>{%a0}";
             ctor_view := Some {| view_requirement := CanonicalObservation;
                                  case_test := "%scrut.has_value()";
                                  case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance mb_get_mapping : OperationMapping (Ref (@mb_get)) :=
  {| operation_headers := ["optional"];
     operation_cpp := Expr "[](const auto& _m, auto _d) { return _m.has_value() ? *_m : _d; }(%arg(m), %arg(d))";
     operation_contract :=
       PureOperation
         [{| argument_name := "m"; argument_use := Read |};
          {| argument_name := "d"; argument_use := Read |}]
         ReturnValue [] |}.
End Mappings.
Import Mappings.

Module MappedOpViewArgument.

Definition deque_fold (l : list nat) (s : PrimString.string) : PrimString.string :=
  fold_left (fun a _ => a) l s.

Definition maybe_get (s : PrimString.string) : PrimString.string := mb_get (Just "abc"%pstring) s.

Definition len (s : PrimString.string) : nat := Z.to_nat (Uint63.to_Z (PrimString.length s)).

Definition result : nat := len (deque_fold [1; 2] "xyz"%pstring) + len (maybe_get "q"%pstring).

End MappedOpViewArgument.

Crane Extraction "mapped_op_view_argument" MappedOpViewArgument.
