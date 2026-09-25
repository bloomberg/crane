(** ITree's own [Recursion.mrec], which reaches C++ with three defects
    stacked in one call.

    [mrec ctx := fun R d => interp_mrec ctx (ctx _ d)].

    1. Fixed: [ctx _ d] was passed to [interp_mrec] as
       [ITree<T3>::ret(ctx(d))] -- a tree wrapped in [ret].  [ctx] is a
       rank-2 [D ~> itree E] parameter, so its application arrives under a
       coercion, and the test for "already a tree" did not look through one.

    2. Fixed: the call named no type arguments, so [mrec]'s result index,
       which no parameter deduces, was left to a deduction that cannot make
       it.  An erased event family made the whole list look unwritable, as if
       it were higher-kinded; it is declared a plain [typename].

    3. Open: [ctx]'s result index is erased with its rank-2 quantifier, so
       [ctx0(d)] is an [ITree<std::any>] where [interp_mrec] wants
       [ITree<T3>]; and [ctx], methodified onto [CountE], is a member
       template whose index an eta lambda cannot supply
       ([tests/wip/eta_handler_event_as_template]).

    Reported by the Vellvm-side session at install #18 (group F). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree Interp.Recursion.
Import ITreeNotations.
Open Scope itree_scope.

Variant CountE : Type -> Type := Count : nat -> CountE nat.

(** Takes a [bool] first, so it stays a function rather than becoming a
    member template of [CountE] -- that shape has a defect of its own
    ([tests/wip/eta_handler_event_as_template]). *)
Definition ctx (verbose : bool) : CountE ~> itree (CountE +' void1) :=
  fun _ e => match e with
             | Count 0 => Ret 0
             | Count (S n) => trigger (inl1 (Count n))
             end.

Module MrecCtxWrappedInRet.
  Definition run : itree void1 nat := mrec (ctx false) (Count 3).
End MrecCtxWrappedInRet.
Crane Extraction "mrec_ctx_wrapped_in_ret" MrecCtxWrappedInRet.
