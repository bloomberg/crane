From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Regression test: module alias inside a functor body shares the same
    short name as a top-level module.  Before the fix, extracting any
    function that caused the whole file to be included (needed_mp_all)
    would trigger an [error_module_clash] crash because [pp_modname] on the
    inner [Module Impl := ...] registered the name in the visible scope,
    clashing with the outer [Module Impl]. *)

Module Type Sig.
  Parameter t : Type.
End Sig.

Module ImplFn (S : Sig).
  Definition foo (x : S.t) : S.t := x.
End ImplFn.

Module LemmasFn (ST : Sig).
  Module Impl := ImplFn ST.
  Definition bar (x : ST.t) : ST.t := Impl.foo x.
End LemmasFn.

Module MySig <: Sig.
  Definition t := nat.
End MySig.

Module Impl := ImplFn MySig.
Module Lemmas := LemmasFn MySig.

Crane Separate Extraction Impl.foo Lemmas.bar.
