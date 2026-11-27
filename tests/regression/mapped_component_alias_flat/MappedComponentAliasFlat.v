(** Found by Ephyra round 28. Variant of round 25's [fn_list_state_alias_fit]
    (fixed for the generic [List]): a typed-mapped container ([maybe A] as
    [std::optional], a test-local [TypeMapping]) at an element type ending in
    a function-type alias, [nat -> st nat] with [st A := nat -> A * nat],
    read by a mapped operation ([mb_get], [_m.has_value() ? *_m : _d]). The
    [Nothing] literal's component was spelled flat through the alias,
    [std::optional<crane::fn<std::pair<uint64_t, uint64_t>(uint64_t,
    uint64_t)>>], while the default lambda was converted to the curried
    [crane::fn<st<uint64_t>(uint64_t)>], so the conditional's operands
    disagreed ("incompatible operand types").

    Fixed: the parameter's type and the literal's annotation differed in the
    erased term argument extraction writes in each type argument's place,
    which a typed mapping never reads, so the two were not seen as one type
    regrouped; a typed-mapped type now carries no term arguments
    ([Types.cpp_ir_of_core_type]).  And a custom constructor whose
    annotation is the slot's type regrouped through an alias is built at
    the slot's type arguments, as a generated inductive's is
    ([Construction.gen_expr_custom_cons]).

    Expected: compiles, [result = 4]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Descriptor.
From Stdlib Require Import List.
Import ListNotations.

Inductive maybe (A : Type) : Type := Nothing | Just (x : A).
Arguments Nothing {A}.
Arguments Just {A} x.
Definition mb_get {A : Type} (m : maybe A) (d : A) : A := match m with Nothing => d | Just x => x end.

Module TM.
Local Open Scope pstring_scope.
#[export] Instance maybe_mapping (A : Type) : TypeMapping (maybe A) :=
  {| type_headers := ["optional"];
     type_cpp := Crane.Cpp.Apply "std::optional" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components := [{| component_name := "element"; component_type := FieldType (Ref (@Just A)) 0 |}];
     type_copy := CopyComponents ["element"]; type_access := ReadOnlyValue (ReadByComponents ["element"]);
     type_views := NoViews (maybe A);
     type_interface := AlgebraicInterface
       [{| ctor_source := Ref (@Nothing A); ctor_build := Expr "std::optional<%stored(element)>{}";
           ctor_view := Some {| view_requirement := CanonicalObservation; case_test := "!%scrut.has_value()"; case_fields := [] |} |};
        {| ctor_source := Ref (@Just A); ctor_build := Expr "std::optional<%stored(element)>{%a0}";
           ctor_view := Some {| view_requirement := CanonicalObservation; case_test := "%scrut.has_value()";
                                case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |}];
     type_model := Structural; type_lifetime := NativeRAII; type_release := OrdinaryRelease; type_numerals := None |}.
#[export] Instance mb_get_mapping : OperationMapping (Ref (@mb_get)) :=
  {| operation_headers := ["optional"];
     operation_cpp := Expr "[](const auto& _m, auto _d) { return _m.has_value() ? *_m : _d; }(%arg(m), %arg(d))";
     operation_contract := PureOperation [{| argument_name := "m"; argument_use := Read |}; {| argument_name := "d"; argument_use := Read |}] ReturnValue [] |}.
End TM.
Import TM.

Module MappedComponentAliasFlat.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition result : nat := fst (mb_get (@Nothing (nat -> st nat)) (fun k : nat => sret k) 4 5).

End MappedComponentAliasFlat.

Crane Extraction "mapped_component_alias_flat" MappedComponentAliasFlat.
