(* A higher-kinded class parameter is named from the dictionary, not the result.

   [TFunctor_list'] is the instance for [fun T => list (F T)], so its emitted
   parameter is [List<T1<std::any>>] with [template <typename> class T1].  The
   only other mention of [T1] is the dictionary, written
   [std::type_identity_t<TFunctor<T1>>] -- a non-deduced context by design.  So
   [T1] can only come from the value argument, and it cannot: Crane wraps every
   such call in an adapter lambda whose parameter it spells [List<std::any>],
   erased one level past the carrier, and matching that against
   [List<T1<std::any>>] leaves [T1] undeduced.

     return TFunctor_list_([](auto&& _ec0, box<std::any> _ec1) {
                             return TFunctor_box(_ec0, _ec1); },
                           _x0, _x1);         // _x1 : List<std::any>

   [on_boxes] was intended as a control -- its Rocq argument is a
   [list (box nat)] with the carrier still on it -- and it is not one: the
   adapter lambda erases at the top-level call too, and both sites failed
   identically.  So the fix cannot be "the top-level case already works".

   The existing recovery, [Translation.hkt_carrier_type_args], reads the
   carrier off the type the *result* is expected to have.  That is unavailable
   here for the same reason the argument is: by the time the call is built the
   expected type is [List<std::any>], already erased.

   What still knows the carrier is the dictionary.  A parameter of class type
   [TFunctor T1] is instantiated by the instance for exactly one type
   constructor, and that instance's method returns [T1] applied -- the
   dictionary for [box] is a function whose codomain is [box B].  So the head
   of the dictionary's codomain *is* the carrier, and
   [Translation.dict_carrier_type_args] reads it there, descending through the
   adapter lambda to the instance the body names.  It writes unconditionally,
   unlike the result route, because the position is non-deduced: even a plain
   template name has to be named rather than left to deduction.

     TFunctor_list_<box>(...)      hk_call_carrier_erased.cpp:25
     TFunctor_outer<List>(...)     hk_call_carrier_erased.cpp:41

   The second one needs [outer<std::any, List<std::any>>] to accept an argument
   of type [outer<std::any, std::any>], which a record kind could not do until
   the record-kind converting constructor landed (221e24961).  Naming a carrier
   trades a deduction failure for a conversion one, so that constructor is a
   precondition of this fix, not an independent improvement.

   Instantiating [TFunctor_list']'s body then exposed a second defect the body
   had been hiding: [tfmap<T1, std::any, std::any>(h, f, _x0)], one argument
   too many.  [Gen_decls.relax_applied_return] moves a return-only type
   variable last and interleaves the synthesised callback parameter before it,
   on the recorded assumption that "nothing supplies this signature's arguments
   explicitly" -- true of a lifted helper, false of a class method, which is
   called with its Rocq arguments written out.  [Translation.writable_tvar_count]
   ends the writable prefix where that reordering starts.

   Vellvm: rocq/Syntax/Traversal.v:859, [TFunctor_modul], the [tfmap f
   (m_globals m)] and [tfmap f (m_declarations m)] lines. *)

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
