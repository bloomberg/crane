(** Crane bug: an instance of a type-constructor class at a type-level
    lambda ([TFunctor (fun T => list (F T))], parametric over [F]) does not
    compile.

    Observed:
      template <typename _CraneTcArg>
      using _crane_carrier_tc_659c8e94e4cfa3a6 = List<box<_CraneTcArg>>;   // before [box] exists
      struct TfunctorComposedInstance {
        ...
        template <typename T1, typename F1>
        static List<T1> TFunctor_list_(std::type_identity_t<TFunctor<T1>> h, F1 &&f, List<T1> x0_);
        ...
            return TFunctor_list_<box>(...)          // a class template for a typename
    Diagnostics:
      error: use of undeclared identifier 'box'
      error: use of undeclared identifier '_crane_carrier_tc_659c8e94e4cfa3a6'
      error: no matching function for call to 'TFunctor_list_'
             (Vellvm: "invalid explicitly-specified argument for template
              parameter 'T1'")
    - the carrier alias for the lambda [fun T => list (box T)] is emitted at
      file scope ahead of the struct that declares [box] (same placement
      problem as partial_app_carrier);
    - [TFunctor_list'] is declared with [F] as a plain [typename T1] and the
      result [List<T1>], i.e. [F] applied at the lambda's variable was
      flattened to [F], but the call site passes the type constructor [box]
      itself.  Unlike an event family, [F] here is a genuine type function:
      [list (F T)] at [T := nat] must be [List<box<Nat>>].

    Reduced from Vellvm, [Syntax/Traversal.v:494-510] ([TFunctor],
    [TFunctor_list], [TFunctor_list']), used by [TypToDtyp.convert_types]:
    [Traversal::template TFunctor_list_<global>(h2, _x0, _x1)] and
    [TFunctor_list_<declaration>] (18 errors). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module TfunctorComposedInstance.
  (* Vellvm's Syntax/Traversal.v *)
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

  #[global] Instance TFunctor_list' {F} `{TFunctor F}
    : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  Record box (T : Set) : Set := Box { unbox : T }.
  Arguments Box {T}.
  Arguments unbox {T}.

  #[global] Instance TFunctor_box : TFunctor box := fun U V f b => Box (f (unbox b)).

  Definition l : list (box nat) :=
    @tfmap (fun T => list (box T)) _ nat nat S [Box 1; Box 2].

  Definition total : nat := fold_left (fun acc b => acc + unbox b) l 0.
  Definition is_five : bool := Nat.eqb total 5.
End TfunctorComposedInstance.

Crane Extraction "tfunctor_composed_instance" TfunctorComposedInstance.
