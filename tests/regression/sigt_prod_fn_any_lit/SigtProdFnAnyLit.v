From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Minimal reproduction of the parse-a-lot LL-parser [bad_any_cast], now fixed.

    The previous repro (sigt_prod_fn_any) stored the predicate/action via a
    *named* [mk] parameter of (abstract, erased) function type, so Crane
    emitted [std::make_pair(std::any(f), std::any(g))] — an explicit
    [std::any(...)] wrap of a variable. That case was handled first.

    But parse-a-lot never calls such an [mk]. It builds each grammar entry with
    *inline lambda literals* placed directly where the erased payload
    [production_semty p = std::pair<std::any, std::any>] is expected (see
    [jsonGrammarEntries] in examples/JSON/Parser/JSON.v). Crane previously
    emitted the two lambdas converted to [std::any] *implicitly* through the
    [std::pair] converting constructor, storing the raw closures — but
    [Parser.h] reads them back with [any_cast<std::function<std::any(std::any)>>],
    which crashed.

    [gen_expr_custom_cons]'s constructor-arg boxing now checks whether the arg
    is a function value (whether or not it is a [CPPlambda]) and routes it
    through [crane_erase_fn], which adapts even *generic* lambdas
    ([ [](const auto&){...} ], produced here because the lambda's domain is the
    abstract [S.sem a]) via a compile-time dispatch on [std::function] CTAD
    viability. This file reproduces the exact inline-lambda-literal shape that
    the earlier fix (a named [mk] parameter) didn't cover. *)

Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

Module Make (S : SEM).

  Definition prod2 : Type := (S.idx * list S.idx)%type.

  Definition pred_ty (p : prod2) : Type :=
    let (a, _) := p in S.sem a -> bool.
  Definition act_ty (p : prod2) : Type :=
    let (a, _) := p in S.sem a -> nat.

  (** production_semty-analog: pair of erased function types -> pair<any,any>. *)
  Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.

  Definition entry : Type := { p : prod2 & psem p }.

  (** Build the entry INSIDE the functor with inline lambda literals whose
      domain is the abstract [S.sem a]. Crane renders these as *generic* lambdas
      [ [](const auto&){...} ] — exactly the predicate/action shape parse-a-lot's
      grammar produces — and now wraps each with [crane_erase_fn] before storing
      it into the [pair<std::any,std::any>] payload. *)
  Definition mk_entry (a : S.idx) : entry :=
    existT psem (a, []) ((fun _ => true), (fun _ => 0)).

  (** Apply the predicate, exactly like Parser.v:113 [if p vs' ...]. *)
  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) fg =>
        let (f, _g) := fg in
        if f (arg a) then true else false
    end.

End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => nat.
End Inst.

Module M := Make Inst.

(** Build the entry via the functor's [mk_entry] (inline generic lambdas at the
    abstract payload type) — mirroring how parse-a-lot builds [jsonGrammarEntries]. *)
Definition my_entry : M.entry := M.mk_entry tt.

Definition my_arg : forall a : Inst.idx, Inst.sem a := fun _ => 0.

(** In Rocq this is [true] (predicate [0 =? 0]), and the extracted C++ now
    agrees. *)
Definition check (u : unit) : bool := M.run my_entry my_arg.

Crane Extraction "sigt_prod_fn_any_lit" check my_entry my_arg.
