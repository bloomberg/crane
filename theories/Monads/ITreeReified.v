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
   - [Ret/Tau/Vis] extract to [ITree] node constructors (not erased)
   - [observe] extracts to method call for pattern matching

   Functions named [main] returning [itree E R] will be extracted as
   [_main] with an automatic wrapper that calls [->run()].

   Re-exports [ITreeBase.v] (shared library erasure directives) and adds
   the reified-mode-specific directives.
*)
From Crane Require Extraction.
From Crane Require Export Monads.ITreeBase.
From ExtLib Require Structures.Monad.

(* Extract itreeF as a custom inductive: the type maps to ITree<R>::variant_t,
   each constructor builds the corresponding node, and the custom match
   template generates an if/else-if chain using holds_alternative and get_if,
   consistent with how Crane generates all other variant pattern matches.

   The constructors deduce [R] from their own argument rather than naming
   [%t1]: inside a function polymorphic in the event type, [itreeF]'s type
   arguments reach here erased, and [%t1] would spell [std::any] where the
   surrounding signature says [T1].  Each is one deducing helper from
   [crane_itree.h], so the deduction lives in the header rather than being
   spelled out in C++ here. *)
Crane Extract Inductive itreeF =>
  "itreeF_t<%t1>"
  [ "itree_ret(%a0)"
    "itree_tau(%a0)"
    "itree_vis(%a0, %a1)" ]
  "if (std::holds_alternative<typename ITree<%t1>::Ret>(%scrut)) { const auto& _itf = *std::get_if<typename ITree<%t1>::Ret>(&%scrut); auto %b0a0 = _itf.value; %br0 } else if (std::holds_alternative<typename ITree<%t1>::Tau>(%scrut)) { const auto& _itf = *std::get_if<typename ITree<%t1>::Tau>(&%scrut); auto %b1a0 = _itf.next; %br1 } else { const auto& _itf = *std::get_if<typename ITree<%t1>::Vis>(&%scrut); auto %b2a0 = _itf.effect; auto %b2a1 = _itf.cont; %br2 }"
  From "crane_itree.h".

(* The ITree library defines Ret/Tau/Vis as Notations. Shadow them with
   Definitions so extraction directives can reference them. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.
Definition Tau {E : Type -> Type} {R : Type} (t : itree E R) : itree E R := Tau t.
Definition Vis {E : Type -> Type} {R X : Type} (e : E X) (k : X -> itree E R)
  : itree E R := Vis e k.

(* [itree] is a coinductive record: its single constructor [go] wraps an
   [itreeF] node, and the node already builds the tree, so [go] is the
   identity.  Without this the notation-level [Ret x] -- which is
   [go (RetF x)] -- reaches C++ as a member [go] of [shared_ptr]. *)
Crane Extract Inductive itree => "std::shared_ptr<ITree<%t1>>" [ "%a0" ] From "crane_itree.h".

Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] =>
  "std::shared_ptr<ITree<%t1>>" From "crane_itree.h".

(* Extract bind as free function itree_bind from crane_itree.h *)
Crane Extract Inlined Constant ITree.bind =>
  "itree_bind(%a0, %a1)" From "crane_itree.h".

(* [MonadNotation]'s [x <- c ;; k] and [ret] go through ExtLib's [Monad]
   class rather than through [ITree.bind]/[Ret] -- which of the two a given
   [;;] means is decided by the notation scope in force at that subterm, so
   one function can easily contain both spellings.  The instance is
   [Monad_itree], which this mode skips, so the class projections reach C++
   with nothing to project from; in this mode they are the itree operations,
   and are spelled as such.  The erased instance argument is not among the
   value arguments, so [%a0]/[%a1] are the operands. *)
Crane Extract Inlined Constant Monad.bind =>
  "itree_bind(%a0, %a1)" From "crane_itree.h".
Crane Extract Inlined Constant Monad.ret =>
  "itree_ret(%a0)" From "crane_itree.h".

(* Extract observe as method call *)
Crane Extract Inlined Constant observe =>
  "%a0->observe()" From "crane_itree.h".

(* [Ret]/[Tau]/[Vis] are spelled exactly as the [itreeF] constructors they
   wrap.  They are not inlined into those constructors: [Ret] is the monad's
   registered return, and the plugin's own handling of it is what turns a
   [Ret tt] into [ITree<void>::ret()]. *)
Crane Extract Inlined Constant Ret =>
  "itree_ret(%a0)" From "crane_itree.h".
Crane Extract Inlined Constant Tau =>
  "itree_tau(%a0)" From "crane_itree.h".
Crane Extract Inlined Constant Vis =>
  "itree_vis(%a0, %a1)" From "crane_itree.h".
