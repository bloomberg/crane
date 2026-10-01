(** Crane bug: the composed instance [TFunctor (fun T => option (F T))]
    builds its [Some] at [std::any].

    Observed (bac0be39f):
      template <typename T1, typename F1>
      std::optional<T1> TFunctor_option(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                        const std::optional<T1> &ot) {
        if (ot.has_value()) { const auto &t0 = *ot;
          return std::make_optional<std::any>(
              std::any(tfmap<T1, std::any, std::any>(h, f, std::any_cast<T1>(t0)))); ...
    [Some (tfmap f t)] should be [std::make_optional<T1>(tfmap<T1, ...>(h, f, t0))].
    Diagnostics:
      error: no viable conversion from returned value of type
             'optional<decay_t<std::any>>' to function return type 'optional<box<std::any>>'
      error: no matching function for call to 'tfmap'   (at the use)
    The list version of the same composed instance
    ([TFunctor_list'], tfunctor_composed_instance) passes.

    Reduced from Vellvm, [Syntax/Traversal.v:508] [TFunctor_option]: two of
    Vellvm's twelve remaining errors on bac0be39f
    ([Traversal::TFunctor_option<Exp<std::any>, ...>] and the [tfmap] call
    that instantiates it). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module TfunctorOptionInstance.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  (* Vellvm's Syntax/Traversal.v:508 *)
  #[global] Instance TFunctor_option {F} `{TFunctor F}
    : TFunctor (fun T => option (F T)) | 50 :=
    fun U V f ot => match ot with None => None | Some t => Some (tfmap f t) end.

  Record box (T : Set) : Set := Box { unbox : T }.
  Arguments Box {T}. Arguments unbox {T}.
  #[global] Instance TFunctor_box : TFunctor box := fun U V f b => Box (f (unbox b)).

  Definition o : option (box nat) := @tfmap (fun T => option (box T)) _ nat nat S (Some (Box 2)).
  Definition is_three : bool := match o with Some b => Nat.eqb (unbox b) 3 | None => false end.
End TfunctorOptionInstance.

Crane Extraction "tfunctor_option_instance" TfunctorOptionInstance.
