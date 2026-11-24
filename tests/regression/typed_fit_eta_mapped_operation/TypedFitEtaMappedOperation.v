(** Found by Ephyra round 24 (whose generator writes its own typed
    mappings), fixed. [mb_get : maybe A -> A -> A] has an
    [OperationMapping], and [maybe] a [TypeMapping] to [std::optional]. At
    [A := nat -> nat], a [let] binds the partial application [mb_get m id]
    where [m] is not a variable; Crane hoists [m] and eta-expands the binder
    to [cf = [=](uint64_t _x0) { return <mb_get template>(_lc1_pa0, id)(_x0); }].
    The eta-expansion's value was typed as the callee's call
    ([Calls.record_call_sig] stamped the callee's codomain, [nat], on the
    immediately invoked lambda binding the hoisted arguments, and
    [Application.eta_fun] typed a call-headed result at the codomain), so
    the typed-fit check under [CRANE_CHECK_IR] put [nat] in the slot of
    [cf]'s type, [nat -> nat].  The C++ was right; extraction failed.  The
    eta-expansion is now typed as the closure it is.

    Expected: extracts under [CRANE_CHECK_IR]; [use [] true = 0],
    [use [1; 2] false = 0]. *)
From Crane Require Import Mapping.NatIntStd.
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

Module TypedFitEtaMappedOperation.

Definition use (l : list nat) : bool -> nat :=
  let cf := mb_get (fold_right (fun (_ : nat) acc => acc) Nothing l) (fun x : nat => x) in
  fun _ : bool => cf 0.

End TypedFitEtaMappedOperation.

Crane Extraction "typed_fit_eta_mapped_operation" TypedFitEtaMappedOperation.
