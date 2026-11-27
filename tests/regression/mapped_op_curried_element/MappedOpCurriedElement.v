(** Found by Ephyra round 24 (whose generator writes its own typed
    mappings). A variant of round 23's [deque_fold_curried_acc]: an
    operation mapping whose template mixes a value of the element type [A]
    with a stored element, at [A := nat -> nat -> nat].  The stored element
    is the flat [crane::fn<uint64_t(uint64_t, uint64_t)>], but the value
    Crane passed or built for [A] was the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>] (or a lambda
    returning a lambda):

    - [deque_map]: [Mapping.DequeList]'s [map] with an identity step over a
      list of two-argument functions: the step was eta-expanded curried and
      [_r.push_back(_f(_x))] had no conversion to the flat element.
    - [maybe_get]: a test-local [OperationMapping] of
      [mb_get : maybe A -> A -> A] as [_m.has_value() ? *_m : _d]:
      "incompatible operand types".

    Fixed: a type variable instantiated at a function type was spelled
    curried, as a template argument and wherever a declaration names the
    variable (Arrow_site Through_tvar), while values of the type are
    spelled flat in every declared position.  A type argument is now
    spelled as the values of its type are ([Types.template_arg_of_core_type]
    at [Declared], [Calls.spell_as_declared]); the arrows a declaration
    writes are one group and the instantiated variable's own arrows the
    next ([Declared_at n]).  The step is now
    [[](crane::fn<uint64_t(uint64_t, uint64_t)> g) { return g; }] and the
    default a flat [crane::fn].

    Expected: compiles; [deque_map [plus; minus] = 2],
    [maybe_get (Just plus) = 3], [maybe_get Nothing = 1]. *)
From Crane Require Import Mapping.NatInt Mapping.Std Mapping.DequeList.
From Corelib Require Import PrimString.
From Crane Require Import Extraction Mapping.Descriptor.
From Stdlib Require Import List.
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

Module MappedOpCurriedElement.

Definition deque_map (l : list (nat -> nat -> nat)) : nat := List.length (map (fun g => g) l).

Definition maybe_get (m : maybe (nat -> nat -> nat)) : nat := mb_get m (fun (x _ : nat) => x) 1 2.

Definition result : nat :=
  deque_map [Nat.add; Nat.sub] * 100 + maybe_get (Just Nat.add) * 10 + maybe_get Nothing.

End MappedOpCurriedElement.

Crane Extraction "mapped_op_curried_element" MappedOpCurriedElement.
