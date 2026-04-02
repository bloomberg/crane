(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Alternative ITree extraction for reified/observable mode.

   Import this module instead of [Monads.ITree] when you need to observe
   or traverse ITree structure (pattern matching on observe, CoFixpoint
   traversals, etc.).

   In reified mode:
   - [itree E R] extracts to [std::shared_ptr<ITree<R>>]
   - [bind] extracts to actual function call (not sequential statements)
   - [Ret/Tau/Vis] extract to constructors (not erased)
   - [observe] extracts to method call for pattern matching

   Functions named [main] returning [itree E R] will be extracted as
   [_main] with an automatic wrapper that calls [->run()].
*)
From Crane Require Extraction.

(** Import the real ITree library. *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps.
From ITree Require Export
     Core.ITreeDefinition
     Core.Subevent
     Indexed.Sum
     Indexed.Function
     Interp.Interp
     Interp.Handler.

Export ITreeNotations.
Open Scope itree_scope.

(* Skip the itree inductive itself to avoid struct generation *)
Crane Extract Skip itree.
Crane Extract Skip ITree.subst.

(* Extract itreeF as a custom inductive: the type maps to ITree<R>::variant_t,
   constructors are empty (only matched, never constructed), and the custom
   match template generates std::visit over the variant. *)
Crane Extract Inductive itreeF =>
  "itreeF_t<%t1>"
  [ "" "" "" ]
  "return std::visit(Overloaded{[&](const typename ITree<%t1>::Ret& _itf) -> decltype(auto) { auto %b0a0 = _itf.value; %br0 }, [&](const typename ITree<%t1>::Tau& _itf) -> decltype(auto) { auto %b1a0 = _itf.next; %br1 }, [&](const typename ITree<%t1>::Vis& _itf) -> decltype(auto) { auto %b2a0 = _itf.effect; auto %b2a1 = _itf.cont; %br2 }}, %scrut);"
  From "crane_itree.h".

(* Skip the ITree module struct — its contents are individually inlined/skipped *)
Crane Extract Skip Module ITree.

(* The ITree library defines Ret/Tau/Vis as Notations. Shadow them with
   Definitions so extraction directives can reference them. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.
Definition Tau {E : Type -> Type} {R : Type} (t : itree E R) : itree E R := Tau t.
Definition Vis {E : Type -> Type} {R X : Type} (e : E X) (k : X -> itree E R)
  : itree E R := Vis e k.

(* Map itree type to std::shared_ptr<ITree<R>> via monad registration *)
Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] =>
  "std::shared_ptr<ITree<%t1>>" From "crane_itree.h".

(* Extract bind as free function itree_bind from crane_itree.h *)
Crane Extract Inlined Constant ITree.bind =>
  "itree_bind(%a0, %a1)" From "crane_itree.h".

(* Extract observe as method call *)
Crane Extract Inlined Constant observe =>
  "%a0->observe()" From "crane_itree.h".

(* Extract constructors - use auto for template deduction *)
Crane Extract Inlined Constant Ret =>
  "ITree<decltype(%a0)>::ret(%a0)" From "crane_itree.h".

Crane Extract Inlined Constant Tau =>
  "[&]() { auto t = %a0; return ITree<decltype(t->run())>::tau(t); }()" From "crane_itree.h".

(* Extract Vis to construct ITree vis nodes.
   Type args are erased, so use itree_vis free function which deduces R
   from the continuation's return type.
   Value args: %a0 = effect (E X), %a1 = continuation (X -> itree E R). *)
Crane Extract Inlined Constant Vis =>
  "itree_vis(%a0, %a1)" From "crane_itree.h".

Crane Extract Inductive sum1 => "" [ "%a0" "%a0" ].
Crane Extract Skip void1.
Crane Extract Inlined Constant elim_void1 => "".
Crane Extract Inlined Constant case_sum1 => "".

Crane Extract Inlined Constant subevent => "%a0".

Crane Extract Skip ITree.map.
Crane Extract Skip ITree.trigger.
Crane Extract Skip ITree.iter.
Crane Extract Skip ITree.forever.
Crane Extract Skip ITree.spin.
Crane Extract Skip ITree.ignore.
Crane Extract Skip ITree.cat.
Crane Extract Skip translate.
Crane Extract Skip translateF.
Crane Extract Skip ITree.subst.

Crane Extract Skip Functor_itree.
Crane Extract Skip Applicative_itree.
Crane Extract Skip Monad_itree.
Crane Extract Skip MonadIter_itree.
Crane Extract Inlined Constant idM => "%a0".

Crane Extract Skip Cat.
Crane Extract Skip Id_.
Crane Extract Skip Inl.
Crane Extract Skip Inr.
Crane Extract Skip Case.
Crane Extract Skip ReSum.
Crane Extract Skip Eq2.
Crane Extract Skip Initial.

Crane Extract Inlined Constant cat => "".
Crane Extract Inlined Constant id_ => "%a0".
Crane Extract Inlined Constant inl_ => "%a0".
Crane Extract Inlined Constant inr_ => "%a0".
Crane Extract Inlined Constant case_ => "".
Crane Extract Inlined Constant resum => "%a0".

Crane Extract Inlined Constant ReSum_id => "%a0".
Crane Extract Inlined Constant ReSum_inl => "%a0".
Crane Extract Inlined Constant ReSum_inr => "%a0".
Crane Extract Inlined Constant ReSum_sum => "%a0".
Crane Extract Inlined Constant ReSum_empty => "".

Crane Extract Skip IFun.
Crane Extract Skip apply_IFun.
Crane Extract Skip apply_IFun'.
Crane Extract Skip as_IFun.
Crane Extract Skip Eq2_IFun.
Crane Extract Skip Id_IFun.
Crane Extract Skip Cat_IFun.
Crane Extract Skip Initial_void1.
Crane Extract Skip Case_sum1.
Crane Extract Skip Inl_sum1.
Crane Extract Skip Inr_sum1.

Crane Extract Inlined Constant subevent_void1 => "".
