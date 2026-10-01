(** Crane bug: [tfmap] over an [option exp] record field (through the
    composed instance [TFunctor (fun T => option (F T))]) names the carrier
    with its inner type erased.

    Observed (e0f2ef0eb), in [TFunctor_global]:
      tfmap<std::optional<std::any>, std::any, std::any>(
          []() { return [](..., std::optional<exp<std::any>> _x1) -> std::optional<exp<std::any>> {
                   return TFunctor_option<exp<std::any>>(...); }; }(),
          f, g.g_exp)
    The carrier is [option (exp T)] at [T := std::any], i.e.
    [std::optional<exp<std::any>>], not [std::optional<std::any>].
    Diagnostic:
      error: no matching function for call to 'tfmap'
      note: no known conversion from '(lambda)' to
            'std::type_identity_t<TFunctor<std::optional<std::any>>>'
    (The list analogue, tfunctor_record_list_field, passes.)

    Reduced from Vellvm, [Syntax/Traversal.v] [TFunctor_global] over
    [LLVMAst.global]'s [g_exp : option exp]:
    [Traversal::template tfmap<std::optional<std::any>, std::any, std::any>(...)]
    -- one of Vellvm's seven remaining errors on e0f2ef0eb. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module TfunctorRecordOptionField.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  #[global] Instance TFunctor_option {F} `{TFunctor F}
    : TFunctor (fun T => option (F T)) | 50 :=
    fun U V f ot => match ot with None => None | Some t => Some (tfmap f t) end.

  Section Syntax.
    Variable T : Set.
    Inductive exp : Set := Lit (t : T) | Neg (e : exp).
    (* Vellvm's LLVMAst [global]: a record with an [option exp] field. *)
    Record global : Set := mk_global { g_typ : T ; g_exp : option exp }.
  End Syntax.
  Arguments Lit {T}. Arguments Neg {T}.
  Arguments mk_global {T}. Arguments g_typ {T}. Arguments g_exp {T}.

  #[global] Instance TFunctor_exp : TFunctor exp :=
    fix go U V f e := match e with Lit t => Lit (f t) | Neg e' => Neg (go U V f e') end.

  (* Traversal.v's [TFunctor_global]. *)
  #[global] Instance TFunctor_global : TFunctor global :=
    fun U V f g => mk_global (f (g_typ g)) (tfmap f (g_exp g)).

  Definition g0 : global nat := mk_global 1 (Some (Lit 2)).
  Definition g1 : global nat := tfmap S g0.
  Definition is_five : bool :=
    match g_exp g1 with Some (Lit n) => Nat.eqb (g_typ g1 + n) 5 | _ => false end.
End TfunctorRecordOptionField.

Crane Extraction "tfunctor_record_option_field" TfunctorRecordOptionField.
