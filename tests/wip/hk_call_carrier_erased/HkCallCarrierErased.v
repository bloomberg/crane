(* Expected: compiles.
   Actual:   error: no matching function for call to 'TFunctor_list_'
             error: no matching function for call to 'TFunctor_outer'
             (plus a [tfmap] failure and two cascades in crane_fn.h)

   The call-site counterpart of hk_instance_body_targ_undeclared.  There the
   generic [list] instance's *body* was wrong; here the bodies are right and
   the *calls* cannot say which carrier they meant.

   [TFunctor_list'] is the instance for [fun T => list (F T)], so its emitted
   parameter is [List<T1<std::any>>] with [template <typename> class T1].  The
   only other mention of [T1] in the signature is the dictionary, written
   [std::type_identity_t<TFunctor<T1>>] -- a non-deduced context by design.  So
   [T1] can only come from the value argument.  It does not: Crane wraps every
   such call in an adapter lambda whose parameter it spells [List<std::any>],
   erased one level past the carrier, and matching that against
   [List<T1<std::any>>] leaves [T1] undeduced.

     return TFunctor_list_([](auto&& _ec0, box<std::any> _ec1) {
                             return TFunctor_box(_ec0, _ec1); },
                           _x0, _x1);         // _x1 : List<std::any>

   The discriminator is the value argument, not the signature.  I had expected
   [on_boxes] to be a control -- its Rocq argument is a [list (box nat)] with
   the carrier still on it -- but it is not: the adapter lambda erases at the
   top-level call too, and both sites fail identically.  Whatever the fix is,
   it is not "the top-level case already works".

   The two sites then come apart under the obvious repair.  Writing the carrier
   by hand:

     TFunctor_list_<box>(...)    closes the error at hk_call_carrier_erased.cpp:25
     TFunctor_outer<List>(...)   does not close the error at :41

   [TFunctor_list_]'s parameter becomes [List<box<std::any>>] and the argument
   is [List<std::any>]; [List] is [IK_Standard], so its converting constructor
   [template <typename _U> List(const List<_U>&)] performs the element cast and
   the call goes through.  [TFunctor_outer]'s parameter becomes
   [outer<std::any, List<std::any>>] against an argument [outer<std::any,
   std::any>], and [outer] is a record kind with no converting constructor at
   all -- so naming the carrier trades a deduction failure for a conversion
   failure.  That is the [Box] defect from partial_application, reached from
   the other direction.

   Both halves matter for the fix.  The axis is not producer-versus-consumer
   and not the carrier's shape: [box] and [List] are both nameable, and
   deduction fails in both places for the same reason.  What decides whether
   naming the carrier is *safe* is which kind sits on the outside of the erased
   argument -- [IK_Standard] container has the constructor, record carrier has
   none.  A repair keyed on the carrier would fire on both; one keyed on the
   argument ("write the carrier where the value argument has lost a level the
   parameter still names") would too.  The record-kind converting constructor
   is the thing that has to exist before either predicate is safe everywhere.

   Closing the [TFunctor_list_] site also uncovers a third failure inside the
   now-instantiated body, at hk_call_carrier_erased.h:203 --
   [tfmap<T1, std::any, std::any>(h, f, _x0)] -- which is hidden today because
   the body is never instantiated.  Worth knowing before the deduction fix
   lands: the count will not simply go down.

   Vellvm: rocq/Syntax/Traversal.v:859, [TFunctor_modul], the [tfmap f
   (m_globals m)] and [tfmap f (m_declarations m)] lines, emitted at
   vellvm_bench.h:12801 and :12807.  Writing [<global>] and [<declaration>]
   there by hand takes Vellvm's extraction from 28 errors to 26 with no
   conversion failure, for the [IK_Standard] reason above. *)

From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.

Section TFunctor.

  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

  #[global] Instance TFunctor_list' {F} `{TFunctor F}
    : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  (* A carrier with an instance: the [F] that the call has to name. *)
  Record box (T : Set) : Set := mk_box { b_payload : T }.
  Arguments mk_box {T}.
  Arguments b_payload {T}.

  #[global] Instance TFunctor_box : TFunctor box | 50 :=
    fun U V f b => mk_box (f (b_payload b)).

  (* The nesting.  [outer] has two parameters, as Vellvm's [modul] does: the
     type index [T] and, separately, the function body [Body].  The instance is
     taken at [fun T => outer T (FnBody T)], so it is a template over [T1] while
     [o_boxes : list (box T)] stays independent of [FnBody] -- which is what
     makes the inner [tfmap] resolve to [TFunctor_list'] with [F := box]. *)
  Record outer (T : Set) (Body : Set) : Set :=
    mk_outer { o_boxes : list (box T); o_body : Body }.
  Arguments mk_outer {T Body}.
  Arguments o_boxes {T Body}.
  Arguments o_body {T Body}.

  #[global] Instance TFunctor_outer {FnBody : Set -> Set} `{TFunctor FnBody}
    : TFunctor (fun T => outer T (FnBody T)) | 50 :=
    fun U V f m => mk_outer (tfmap f (o_boxes m)) (tfmap f (o_body m)).

End TFunctor.

Module HkCallCarrierErased.

  Definition bump (n : nat) : nat := S n.

  (* Intended as a control -- the Rocq argument still has the carrier on it.
     It is not one: the adapter lambda erases here too.  See the header. *)
  Definition on_boxes (l : list (box nat)) : list (box nat) := tfmap bump l.

  (* The record-kind half: forces [TFunctor_outer] to be emitted and called. *)
  Definition on_outer (m : outer nat (list nat)) : outer nat (list nat) := tfmap bump m.

End HkCallCarrierErased.

Crane Extraction "hk_call_carrier_erased" HkCallCarrierErased.
