From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

(** Same shape as sigt_prod_fn_any_lit (grammar entry = sigma-type pairing a
    production with an erased predicate/action pair), but here the
    predicate/action *domain* is itself a concrete pair `sem a * unit`
    (mirroring [symbols_semty ys := symbol_semty y * symbols_semty ys'] in
    theories/Parser/Defs.v), so the inline generic lambda body structurally
    destructures its argument via `let (v, _x) := tup`.

    This used to fail to *compile*: the lambda is stored via [crane_erase_fn]
    (its domain is partly erased), so at runtime it is only ever invoked with
    its whole argument boxed as a single raw [std::any] — but the generated
    parameter was a generic [auto&] that, once deduced as [std::any], can't be
    destructured via a structured binding ([std::any] is not tuple-like).
    Fixed by [mark_own_param_for_pair_erasure] (translation.ml): when a
    lambda literal is about to be routed through [crane_erase_fn], its
    immediate self-match on its own parameter is marked [MLmagic] so the
    scrutinee is any_cast to [pair<any,any>] before destructuring, matching
    what [run]'s application site actually constructs and passes. *)
Module Make (S : SEM).
  Definition dom (a : S.idx) : Type := (S.sem a * unit)%type.
  Definition prod2 : Type := (S.idx * list S.idx)%type.
  Definition pred_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition act_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.
  Definition entry : Type := { p : prod2 & psem p }.

  Definition mk_entry (a : S.idx) : entry :=
    existT psem (a, [])
      ((fun tup : dom a => let (v, _x) := tup in let _ := v in true),
       (fun tup : dom a => let (v, _x) := tup in let _ := v in true)).

  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) fg =>
        let (f, _g) := fg in
        if f (arg a, tt) then true else false
    end.
End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => bool.
End Inst.

Module M := Make Inst.
Definition my_entry : M.entry := M.mk_entry tt.
Definition my_arg : forall a : Inst.idx, Inst.sem a := fun _ => true.
Definition check (u : unit) : bool := M.run my_entry my_arg.
Crane Extraction "sigt_prod_fn_any_lit_pair" check my_entry my_arg.
