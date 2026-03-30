(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Bridge between the InteractionTrees library (DeepSpec/InteractionTrees)
   and Crane's extraction pipeline.

   This file imports the real ITree library and adds all extraction directives
   needed to erase the ITree infrastructure during C++ code generation.
   Effect types compose via [+'] and automatic injection via [E -< F].
*)
From Crane Require Extraction.

(** Import the real ITree library.
    [Basics.Basics] is imported non-exportingly because it defines
    [Notation void := Empty_set] which conflicts with Crane's [void]. *)
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

(** Re-export the library's monad notations (in [itree_scope]). *)
Export ITreeNotations.
Open Scope itree_scope.

(** ------------------------------------------------------------------ *)
(** Core ITree type erasure                                             *)
(** ------------------------------------------------------------------ *)

Crane Extract Skip itree.
Crane Extract Skip itreeF.
Crane Extract Inlined Constant observe => "".
Crane Extract Skip ITree.subst.

(* Skip the ITree module struct — its contents are individually skipped/erased *)
Crane Extract Skip Module ITree.

(** The ITree library defines [Ret] as a [Notation]. We shadow it with
    a [Definition] so Crane's monad registration can reference it as a
    global. Users still write [Ret x] — the Definition has the same
    behavior as the Notation it shadows. *)
Definition Ret {E : Type -> Type} {R : Type} (x : R) : itree E R := Ret x.

Crane Extract Monad itree [ bind := ITree.bind , ret := Ret ] => "%t1".

(** ------------------------------------------------------------------ *)
(** Effect sum erasure                                                  *)
(** ------------------------------------------------------------------ *)

Crane Extract Inductive sum1 => "" [ "%a0" "%a0" ].
Crane Extract Skip void1.
Crane Extract Inlined Constant elim_void1 => "".
Crane Extract Inlined Constant case_sum1 => "".

(** ------------------------------------------------------------------ *)
(** Subevent erasure                                                    *)
(** ------------------------------------------------------------------ *)

Crane Extract Inlined Constant subevent => "%a0".

(** ------------------------------------------------------------------ *)
(** ITree operations erasure                                            *)
(** ------------------------------------------------------------------ *)

Crane Extract Skip ITree.map.
Crane Extract Skip ITree.trigger.
Crane Extract Skip ITree.iter.
Crane Extract Skip ITree.forever.
Crane Extract Skip ITree.spin.
Crane Extract Skip ITree.ignore.
Crane Extract Skip ITree.cat.
Crane Extract Skip translate.
Crane Extract Skip translateF.

(** ------------------------------------------------------------------ *)
(** ExtLib instance erasure                                             *)
(** ------------------------------------------------------------------ *)

Crane Extract Skip Functor_itree.
Crane Extract Skip Applicative_itree.
Crane Extract Skip Monad_itree.
Crane Extract Skip MonadIter_itree.
Crane Extract Inlined Constant idM => "%a0".

(** ------------------------------------------------------------------ *)
(** Category infrastructure erasure                                     *)
(** ------------------------------------------------------------------ *)

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
