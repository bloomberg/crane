(** Crane bug(s): ITree's subevent machinery ([trigger], [subevent],
    [ReSum IFun], the [ReSum_inl]/[ReSum_id] instances over [Cat_IFun]/
    [Id_IFun]) does not compile under vanilla extraction.  This is one
    library feature rather than one defect; the layers seen:

    1. [IFun E F := forall T, E T -> F T] is declared with template-template
       parameters,
         template <template <typename> class e, template <typename> class f>
         using IFun = std::function<f<std::any>(e<std::any>)>;
       but every use passes erased families: [IFun<std::any, std::any>].
         error: template argument for template template parameter must be a
                class template or type alias template
       In Vellvm this one message accounts for ~2440 of ~5580 errors.
    2. [Subevent::subevent] takes [template <typename> class T2] for the
       target family while callers pass the family as a plain type
       (after coind_family_param, [Itree<E, R>] takes [E] as a typename):
         error: call to non-static member function without an object argument
       (clang's message when no candidate's template parameters fit; ~2610
       of Vellvm's errors).
    3. [template <typename obj = void, typename c> using ReSum = c;]
         error: template parameter missing a default argument
         error: no template named 'ReSum'
       and then [no matching function for call to 'ReSum_inl' / 'ReSum_id'].

    Guess, labelled as one: with event families now plain typenames (the
    coind_family_param fix, point 2), a family applied at an index ([F T])
    wants to be just [F] everywhere, as [VisF]'s field already is.

    Reduced from Vellvm's vanilla-ITree extraction; every event-raising
    helper (e.g. [LLVMEvents.gwrite], [Semantics/LLVMEvents.v]) is
    [trigger (GlobalWrite ...)] through [subevent]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module ItreeTriggerSubevent.
  Variant fooE : Type -> Type := Foo : nat -> fooE nat.
  Variant barE : Type -> Type := Bar : barE unit.

  (* trigger goes through ITree.Subevent's [subevent] (ReSum IFun). *)
  Definition t : itree (fooE +' barE) nat := trigger (Foo 2).

  Definition is_foo_two : bool :=
    match _observe t with
    | VisF e _ => match e with inl1 (Foo n) => Nat.eqb n 2 | inr1 _ => false end
    | _ => false
    end.
End ItreeTriggerSubevent.

Crane Extraction "itree_trigger_subevent" ItreeTriggerSubevent.
