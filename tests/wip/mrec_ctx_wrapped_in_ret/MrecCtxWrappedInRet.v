(** ITree's own [Recursion.mrec], which reaches C++ with defects stacked
    in one call.  [mrec ctx := fun R d => interp_mrec ctx (ctx _ d)].

    1. Fixed: [ctx _ d] was passed to [interp_mrec] wrapped in [ret].
    2. Fixed: the call named no type arguments for [mrec]'s undeducible
       result index.
    3. Fixed 2026-11-24: [ctx], methodified onto [CountE<ptr>], was declared
       returning [ITree<ptr>]: the method renumbering mapped the receiver's
       type argument (the phantom index of [CountE]) onto the struct's first
       variable, which is the promoted [ptr], and the call dropped it as
       carried.  The receiver's arguments now land after the promoted
       parameters, a killed phantom is the method's own variable on both
       sides, and the method value writes its unsupplied index erased:
       [_x0.template ctx<_tcI0, crane::obj>(false)].

    4. Open (diagnosed 2026-11-24): in [Recursion::mrec], [ctx0(d)] -- the
       rank-2 parameter [ctx : D ~> itree (D +' E)] applied at [R] -- is an
       [ITree<crane::obj>] (its index erased with the quantifier, to
       [Unknown], so extraction records no coercion), while [interp_mrec]
       takes [ITree<T3>].  It needs [crane_convert<std::shared_ptr<ITree<T3>>>]
       on the consumer side; see handler_lambda_targ_undeclared for why
       nothing decides that today.

    Reported by the Vellvm-side session at install #18 (group F). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree Interp.Recursion.
Import ITreeNotations.
Open Scope itree_scope.

Class Params := { ptr : Type ; nullp : ptr }.

Section S.
  Context {Pa : Params}.

  (** Carries a promoted type, so it is a class template, as Vellvm's
      [CallE] is: named as a type argument it needs its promoted arguments. *)
  Variant CountE : Type -> Type := Count : nat -> ptr -> CountE nat.

  (** Takes a [bool] first; it is still made a member template of
      [CountE], its receiver the event after the [bool]. *)
  Definition ctx (verbose : bool) : CountE ~> itree (CountE +' void1) :=
    fun _ e => match e with
               | Count 0 _ => Ret 0
               | Count (S n) p => trigger (inl1 (Count n p))
               end.

  Definition run_mrec : itree void1 nat := mrec (ctx false) (Count 3 nullp).
End S.

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module MrecCtxWrappedInRet.
  Definition run : itree void1 nat := @run_mrec natParams.
End MrecCtxWrappedInRet.
Crane Extraction "mrec_ctx_wrapped_in_ret" MrecCtxWrappedInRet.
