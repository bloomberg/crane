(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Reified ITree extraction mode.

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

   Re-exports [ITreeBase.v] (shared library erasure directives) and adds
   the reified-mode-specific directives.
*)
From Crane Require Extraction.
From Crane Require Export Monads.ITreeBase.

(* Extract itreeF as a custom inductive: the type maps to ITree<R>::variant_t,
   constructors are empty (only matched, never constructed), and the custom
   match template generates std::visit over the variant. *)
Crane Extract Inductive itreeF =>
  "itreeF_t<%t1>"
  [ "" "" "" ]
  "return std::visit(Overloaded{[&](const typename ITree<%t1>::Ret& _itf) -> decltype(auto) { auto %b0a0 = _itf.value; %br0 }, [&](const typename ITree<%t1>::Tau& _itf) -> decltype(auto) { auto %b1a0 = _itf.next; %br1 }, [&](const typename ITree<%t1>::Vis& _itf) -> decltype(auto) { auto %b2a0 = _itf.effect; auto %b2a1 = _itf.cont; %br2 }}, %scrut);"
  From "crane_itree.h".

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
