(** Crane bug (runtime): inside a definitional-class instance over an alias
    [mcfg T := @modul T (cfg T)] ([ConvertTyp_mcfg : ConvertTyp mcfg :=
    fun k => tfmap ...]), the [tfmap] carrier is written with the inner
    [cfg T] erased: [modul<std::any, std::any>] instead of
    [modul<std::any, cfg<std::any>>] (= [mcfg<std::any>]).

    Observed (post-interp_state_after_interp HEAD):
      static inline const ConvertTyp<mcfg> ConvertTyp_mcfg = []() {
        return [](Nat k, mcfg<Nat> eta0_) {
          return tfmap<modul<std::any, std::any>, Nat, Nat>(
              []() { return [](..., const auto &_x1) -> modul<std::any, cfg<std::any>> {...}; }(), ...
    It compiles; at run time the conversion between the two modul
    instantiations any_casts a [cfg] out of a [std::any] that does not hold
    one:
      libc++abi: terminating due to uncaught exception of type
      std::bad_any_cast: bad any cast
    Calling [tfmap] at [mcfg nat] directly (not through the class instance)
    runs correctly.

    Reduced from Vellvm, [Syntax/TypToDtyp.v:341] ([ConvertTyp_mcfg]),
    [Syntax/CFG.v:57-73] ([modul], [mcfg := @modul cfg]) and
    [Syntax/Traversal.v:883] ([TFunctor_mcfg]): with the let-bound family
    hand-fixed, the Vellvm binary throws this from
    [TypToDtyp::convert_types] ([Traversal::tfmap<modul<std::any, std::any>, Typ, Dtyp>]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module TfunctorAliasOfApplied.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.
  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.
  #[global] Instance TFunctor_list' {F} `{TFunctor F}
    : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  (* Vellvm's CFG.v: a module record over [T] and a body type [FnBody], and
     [mcfg T := modul T (cfg T)]. *)
  Section Syntax.
    Variable T : Set.
    Record cfg : Set := mkCFG { blk : T }.
    Record definition {FnBody : Set} : Set := mk_def { df_ty : T ; df_body : FnBody }.
    Record modul {FnBody : Set} : Set := mk_modul { m_defs : list (@definition FnBody) }.
    Definition mcfg : Set := @modul cfg.
  End Syntax.
  Arguments mkCFG {T}. Arguments blk {T}.
  Arguments mk_def {T FnBody}. Arguments df_ty {T FnBody}. Arguments df_body {T FnBody}.
  Arguments mk_modul {T FnBody}. Arguments m_defs {T FnBody}.

  #[global] Instance TFunctor_cfg : TFunctor cfg := fun U V f c => mkCFG (f (blk c)).
  #[global] Instance TFunctor_definition {FnBody} `{TFunctor FnBody}
    : TFunctor (fun T => @definition T (FnBody T)) :=
    fun U V f d => mk_def (f (df_ty d)) (tfmap f (df_body d)).
  (* Traversal.v:883 *)
  #[global] Instance TFunctor_mcfg {FnBody} `{TFunctor FnBody}
    `{TFunctor (fun T => @definition T (FnBody T))}
    : TFunctor (fun T => @modul T (FnBody T)) | 50 :=
    fun U V f p => mk_modul (tfmap f (m_defs p)).

  (* TypToDtyp.v:341 [ConvertTyp_mcfg := fun env => tfmap (typ_to_dtyp env)] *)
  Class ConvertTyp (F : Set -> Set) : Type := convert_typ : nat -> F nat -> F nat.
  #[global] Instance ConvertTyp_mcfg : ConvertTyp mcfg := fun k => tfmap (fun n => n + k).
  Definition convert (m : mcfg nat) : mcfg nat := convert_typ 1 m.

  Definition m0 : mcfg nat := mk_modul [mk_def 1 (mkCFG 2)].
  Definition total : nat :=
    match m_defs (convert m0) with d :: _ => df_ty d + blk (df_body d) | [] => 0 end.
  Definition is_five : bool := Nat.eqb total 5.
End TfunctorAliasOfApplied.

Crane Extraction "tfunctor_alias_of_applied" TfunctorAliasOfApplied.
