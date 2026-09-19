(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared ITree library erasure directives.

   Imports the real InteractionTrees library and provides extraction
   Skip/Inline directives for the library infrastructure that must be
   erased regardless of extraction mode (erased vs reified).

   Both [ITree.v] (erased mode) and [ITreeReified.v] (reified mode)
   re-export this module and add their mode-specific directives.
*)
From Crane Require Extraction.

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

(* A sum of event families is a real type: a handler over [E +' F] matches on
   which side the event came from, and the answer is not in the type.  The
   index the families are applied at is erased, so the two parameters are the
   event structs themselves. *)
Crane Extract Inductive sum1 => "Sum1"
  [ "sum1_inl(%a0)" "sum1_inr(%a0)" ]
  From "crane_itree.h".
Crane Extract Skip void1.
Crane Extract Inlined Constant elim_void1 => "".
Crane Extract Inlined Constant case_sum1 => "".

Crane Extract Inlined Constant subevent => "%a0".

Crane Extract Skip Embeddable.
Crane Extract Inlined Constant embed => "%a0".
Crane Extract Skip Embeddable_itree.
Crane Extract Skip Embeddable_forall.

Crane Extract Skip ITree.map.
(* [iter] is not skipped: it is reached through [MonadIter], whose instance for
   trees the mode skips, so a skipped [iter] leaves a call with no callee at
   all -- [return <E, I, R>(...)].  The helper builds the same [Tau]-guarded
   tree the Rocq definition denotes. *)
Crane Extract Inlined Constant ITree.iter =>
  "itree_iter(%a0, %a1)" From "crane_itree.h".
Crane Extract Skip ITree.forever.
Crane Extract Skip ITree.spin.
Crane Extract Skip ITree.ignore.
Crane Extract Skip ITree.cat.
(* Relabelling a reified tree's events is the identity: a [Vis] stores its
   effect as a thunk, so the event family it was written at is already gone
   from the representation.  Skipped, [translate] left a call with no callee;
   what it means here is the tree it was given. *)
Crane Extract Inlined Constant translate => "%a1" From "crane_itree.h".
Crane Extract Skip translateF.

Crane Extract Skip Functor_itree.
Crane Extract Skip Applicative_itree.
(* Not skipped, unlike its siblings: a tree's [bind] and [ret] are named by
   their own mappings wherever they are written directly, but a generic
   definition constrained by [Monad] has a dictionary parameter that must be
   given a type -- [Monad_stateT<Monad_itree, S>].  The header supplies one. *)
Crane Extract Inlined Constant Monad_itree => "Monad_itree<%t0>" From "crane_itree.h".
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
(* [case_ f g] reads which side of a sum an event came from.  Skipped, it left
   a call with no callee at all; and it cannot be spelled as a dispatch
   written out here, because the same constant is written both bare -- as the
   handler an [interp] is given -- and applied to an event.  The helper is a
   value, so it is both: what the template does not name, the use site
   applies it to. *)
Crane Extract Inlined Constant case_ =>
  "itree_case(%a1, %a2)" From "crane_itree.h".
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

Crane Extract Skip ITree.subst.
Crane Extract Skip Module ITree.
