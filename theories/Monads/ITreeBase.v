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

Crane Extract Inductive sum1 => "" [ "%a0" "%a0" ].
Crane Extract Skip void1.
Crane Extract Inlined Constant elim_void1 => "".
Crane Extract Inlined Constant case_sum1 => "".

Crane Extract Inlined Constant subevent => "%a0".

Crane Extract Skip Embeddable.
Crane Extract Inlined Constant embed => "%a0".
Crane Extract Skip Embeddable_itree.
Crane Extract Skip Embeddable_forall.

Crane Extract Skip ITree.map.
Crane Extract Skip ITree.trigger.
Crane Extract Skip ITree.iter.
Crane Extract Skip ITree.forever.
Crane Extract Skip ITree.spin.
Crane Extract Skip ITree.ignore.
Crane Extract Skip ITree.cat.
Crane Extract Skip translate.
Crane Extract Skip translateF.

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

Crane Extract Skip itree.
Crane Extract Skip ITree.subst.
Crane Extract Skip Module ITree.
