(** Crane bug: a custom match whose scrutinee is computed by an invoked
    lambda holding custom matches of its own reached the printer with the
    inner matches' templates uninstantiated:
      Anomaly "Crane: a declaration reached the printer holding an
      uninstantiated custom match, which only a lowered declaration may
      hold in CustomMatchLambdaScrutinee.dtyp_base_eq_dec"

    [decide equality] on a [positive] field gives
    [sumbool_rec _ _ _ (positive_rec _ _ _ _ p q)]: a [sumbool] match
    (mapped to [if], {!Mapping.Shared}) on a local recursive function whose
    body matches on [sumbool] again.  The instantiation pass rewrote a
    custom match's branches but not its scrutinee.

    Reduced from Vellvm's [DynamicTypes.dtyp_base_eq_dec]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import ZArith.

Module CustomMatchLambdaScrutinee.
  Variant fpv : Set := FP_Half | FP_Float | FP_Double.

  Unset Elimination Schemes.
  Variant dtyp_base : Set :=
  | DTYPE_I (sz : positive)
  | DTYPE_Iptr
  | DTYPE_FP (fp : fpv)
  | DTYPE_B (sz : positive).
  Set Elimination Schemes.

  Lemma dtyp_base_eq_dec : forall (t1 t2 : dtyp_base), {t1 = t2} + {t1 <> t2}.
  Proof. repeat decide equality. Defined.

  Definition dtyp_base_eqb (a b : dtyp_base) : bool :=
    if dtyp_base_eq_dec a b then true else false.

  Definition same_i : bool := dtyp_base_eqb (DTYPE_I 32) (DTYPE_I 32).
  Definition diff_i : bool := dtyp_base_eqb (DTYPE_I 32) (DTYPE_I 64).
  Definition diff_ctor : bool := dtyp_base_eqb (DTYPE_I 8) (DTYPE_B 8).
  Definition same_fp : bool := dtyp_base_eqb (DTYPE_FP FP_Float) (DTYPE_FP FP_Float).
  Definition diff_fp : bool := dtyp_base_eqb (DTYPE_FP FP_Float) (DTYPE_FP FP_Double).
End CustomMatchLambdaScrutinee.

Crane Extraction "custom_match_lambda_scrutinee" CustomMatchLambdaScrutinee.
