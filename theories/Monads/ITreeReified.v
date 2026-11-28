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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** Extract itreeF as a custom inductive: the type maps to ITree<R>::variant_t,
   each constructor builds the corresponding node, and the custom match
   template generates an if/else-if chain using holds_alternative and get_if,
   consistent with how Crane generates all other variant pattern matches.

   The constructors deduce [R] from their own argument rather than naming
   [%t1]: inside a function polymorphic in the event type, [itreeF]'s type
   arguments reach here erased, and [%t1] would spell [std::any] where the
   surrounding signature says [T1].  Each is one deducing helper from
   [crane_itree.h], so the deduction lives in the header rather than being
   spelled out in C++ here. *)
#[export] Instance itreeF_mapping (E : Type -> Type) (R T : Type) : TypeMapping (itreeF E R T) :=
  {| type_headers := ["crane_itree.h"];
     type_cpp := Crane.Cpp.Apply "itreeF_t" [Crane.Cpp.TypeArg (Crane.Cpp.SourceType R)];
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (itreeF E R T);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@RetF E R T);
             ctor_build := Expr "itree_ret(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "std::holds_alternative<typename ITree<%t1>::Ret>(%scrut)";
                       case_fields :=
                         [(0, OwnedProjection "std::get_if<typename ITree<%t1>::Ret>(&%scrut)->value")] |} |};
          {| ctor_source := Ref (@TauF E R T);
             ctor_build := Expr "itree_tau(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "std::holds_alternative<typename ITree<%t1>::Tau>(%scrut)";
                       case_fields :=
                         [(0, OwnedProjection "std::get_if<typename ITree<%t1>::Tau>(&%scrut)->next")] |} |};
          {| ctor_source := Ref (@VisF E R T);
             ctor_build := Expr "itree_vis(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "std::holds_alternative<typename ITree<%t1>::Vis>(%scrut)";
                       case_fields :=
                         [(0, OwnedProjection
                                "crane_event_as<%ret>(std::get_if<typename ITree<%t1>::Vis>(&%scrut)->effect)");
                          (1, OwnedProjection "std::get_if<typename ITree<%t1>::Vis>(&%scrut)->cont")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** The ITree library defines Ret/Tau/Vis as Notations. Shadow them with
   Definitions so extraction directives can reference them. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.
(** Shadows the [Tau] notation. *)
Definition Tau {E : Type -> Type} {R : Type} (t : itree E R) : itree E R := Tau t.
(** Shadows the [Vis] notation. *)
Definition Vis {E : Type -> Type} {R X : Type} (e : E X) (k : X -> itree E R)
  : itree E R := Vis e k.

(** [itree] is a coinductive record: its single constructor [go] wraps an
   [itreeF] node, and the node already builds the tree, so [go] is the
   identity.  Without this the notation-level [Ret x] -- which is
   [go (RetF x)] -- reaches C++ as a member [go] of [shared_ptr]. *)
#[export] Instance itree_mapping (E : Type -> Type) (R : Type) : TypeMapping (itree E R) :=
  {| type_headers := ["crane_itree.h"];
     type_cpp :=
       Crane.Cpp.Apply "std::shared_ptr"
         [Crane.Cpp.TypeArg (Crane.Cpp.Apply "ITree" [Crane.Cpp.TypeArg (Crane.Cpp.SourceType R)])];
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (itree E R);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@go E R);
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields := [(0, OwnedProjection "%scrut->observe()")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [itree] is a monad over [std::shared_ptr<ITree<R>>] trees. *)
Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] =>
  "std::shared_ptr<ITree<%t1>>" From "crane_itree.h".

(** [ITree.bind] is [itree_bind], which builds the bound tree. *)
#[export] Instance bind_mapping : OperationMapping (Ref (@ITree.bind)) :=
  builds ["crane_itree.h"] ["u"; "k"] (Structured (Call "itree_bind" [] [Arg "u"; Arg "k"])).

(** [MonadNotation]'s [x <- c ;; k] and [ret] go through ExtLib's [Monad]
   class rather than through [ITree.bind]/[Ret] -- which of the two a given
   [;;] means is decided by the notation scope in force at that subterm, so
   one function can easily contain both spellings.  The instance is
   [Monad_itree], which this mode skips, so the class projections reach C++
   with nothing to project from; in this mode they are the itree operations,
   and are spelled as such.  The instance argument is not among the
   contract's arguments.

   A mapping on a class field is written for the monad whose instance the mode
   skipped, so it only applies where the instance {e was} skipped: a monad of
   the user's own keeps its instance, and that instance names its own
   operations. *)
#[export] Instance monad_bind_mapping : OperationMapping (Ref (@Monad.bind)) :=
  builds ["crane_itree.h"] ["t"; "k"] (Structured (Call "itree_bind" [] [Arg "t"; Arg "k"])).
(** [Monad.ret] at [itree] is [itree_ret]. *)
#[export] Instance monad_ret_mapping : OperationMapping (Ref (@Monad.ret)) :=
  builds ["crane_itree.h"] ["x"] (Structured (Call "itree_ret" [] [Arg "x"])).


(** A reified tree keeps the node an event is triggered at, so [trigger] is a
   real [Vis] here (the erased mode, which performs the event on the spot,
   skips it).  The helper deduces the tree's result type at the use site: it is
   an index of the event type and so has no spelling of its own where the
   trigger is written. *)
#[export] Instance trigger_mapping : OperationMapping (Ref (@ITree.trigger)) :=
  builds ["crane_itree.h"] ["e"] (Structured (Call "itree_trigger" [] [Arg "e"])).

(** [translate h t] applies [h] to every event of [t].  It is not the
   identity even for an injection: a [Vis] keeps the side an [inl1] or [inr1]
   names, and a handler over the sum reads it.  Its value arguments are the
   handler and the tree; the two event families come first, erased. *)
#[export] Instance translate_mapping : OperationMapping (Ref (@translate)) :=
  builds ["crane_itree.h"] ["h"; "t"] (Structured (Call "itree_translate" [] [Arg "h"; Arg "t"])).
(** [observe] is the node's [observe] method,
    exposing the [itreeF] node to match on. *)
#[export] Instance observe_mapping : OperationMapping (Ref (@observe)) :=
  effect_cpp ["crane_itree.h"] ["t"] (Expr "%arg(t)->observe()").

(** [Ret]/[Tau]/[Vis] are spelled exactly as the [itreeF] constructors they
   wrap.  They are not inlined into those constructors: [Ret] is the monad's
   registered return, and the plugin's own handling of it is what turns a
   [Ret tt] into [ITree<void>::ret()]. *)
#[export] Instance Ret_mapping : OperationMapping (Ref (@Ret)) :=
  builds ["crane_itree.h"] ["x"] (Structured (Call "itree_ret" [] [Arg "x"])).
(** [Tau] is [itree_tau]. *)
#[export] Instance Tau_mapping : OperationMapping (Ref (@Tau)) :=
  builds ["crane_itree.h"] ["t"] (Structured (Call "itree_tau" [] [Arg "t"])).
(** [Vis] is [itree_vis]. *)
#[export] Instance Vis_mapping : OperationMapping (Ref (@Vis)) :=
  builds ["crane_itree.h"] ["e"; "k"] (Structured (Call "itree_vis" [] [Arg "e"; Arg "k"])).
