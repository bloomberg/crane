(* Expected: compiles.
   Actual:   three errors, all from one emitted helper:

     hk_carrier_written_at_partial_app.cpp:5:50: use of template template
       parameter '_F0' requires template arguments
     :13:32: use of undeclared identifier 'T1'
     :13:37: 'template' keyword not permitted here

   The sibling of [pattern_lambda_binder_over_erased] reached by writing the
   inner map point-free.  [tfmap f] is a partial application of a class
   method, so the carrier the dictionary supplies has to be written at the
   call, and the recovered carrier comes out wrong in two separate ways:

     template <template <typename> class _F0> struct _crane_carrier_tch {
       template <typename _CraneTcArg>
       using c = std::function<Exp0<_CraneTcArg>(Exp0<_F0>)>;
     };
     ... tfmap<_crane_carrier_tch<T1>::template c>(h, f) ...

   The alias writes [Exp0<_F0>], applying the carrier to a template-template
   parameter instead of applying that parameter to an argument -- the well
   formed shape is [_F0<_CraneTcArg>].  And the use writes [T1], which names
   a template parameter of a scope this function is not in; [TFunctor_phi] is
   not a template.

   NOT the Vellvm [_crane_carrier_tch] error, which is a redefinition: that
   helper carries a fixed name and is emitted once per carrier site, so two
   sites collide (vellvm_bench.cpp:5 against :173).  Same helper, different
   defect; this one is reached from Crane's own tests. *)

From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.

Class TFunctor (T : Set -> Set) :=
  tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

Inductive exp (T : Set) : Set := Var (t : T) | Lit (n : nat).
Arguments Var {T}.
Arguments Lit {T}.

#[global] Instance TFunctor_list : TFunctor list := fun U V f l => List.map f l.

#[global] Instance TFunctor_exp : TFunctor exp :=
  fun U V f e => match e with Var t => Var (f t) | Lit n => Lit n end.

Inductive phi (T : Set) : Set := Phi (es : list (exp T)).
Arguments Phi {T}.

(** The shape under test: [tfmap f] applied to nothing, mapped over the list.
    The dictionary [h] is a hypothesis, so the carrier cannot be resolved at
    the definition and must be written at the partial application. *)
Section WithExp.
  Context `{h : TFunctor exp}.

  #[global] Instance TFunctor_phi : TFunctor phi :=
    fun U V f p => match p with Phi es => Phi (List.map (tfmap f) es) end.
End WithExp.

Module HkCarrierWrittenAtPartialApp.

  Definition bump (n : nat) : nat := S n.

  Definition on_phi (p : phi nat) : phi nat := tfmap bump p.

End HkCarrierWrittenAtPartialApp.

Crane Extraction "hk_carrier_written_at_partial_app" HkCarrierWrittenAtPartialApp.
