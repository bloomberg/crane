(* A type variable used as the event family of a reified tree is kinded
   [typename], not [template <typename> class].

   `trigger_cast'` applies [E] in its domain ([e : E void]), which is the
   usual evidence for a higher kind, and the application makes the parameter
   [T1<Void0>].  Nothing can be passed there.  An event family is emitted as a
   plain [struct] -- a [Type -> Type] inductive whose constructors sit at
   differing indices has no C++ template to be -- so there is no template name
   in the program, and the call spelled [std::any] for a parameter that could
   not take a type at all:

     std::shared_ptr<ITree<T2>> trigger_cast_(T1<Void0> e);   // T1 a template
     return trigger_cast_<std::any, T2>(UBE::throwub(std::monostate{}));
     // error: invalid explicitly-specified argument for template parameter T1

   The fix reads the family from the tree rather than from the application:
   [Ml_type_util.event_family_ml_tvars] collects the variables an ML signature
   hands to a reified monad's event position, and
   {!Ml_type_util.higher_kinded_ml_tvars} refuses the higher kind for those.
   The application is then taken back off by the machinery that was already
   there for a refused kind, [Gen_decls.deapply_plain_tvars], leaving
   [trigger_cast_(T1 e)] with [T1] the event struct itself -- which is what
   reaches C++, since the index it was applied at is erased.

   Note this is narrower than "demote higher-kinded parameters": the Vellvm
   artifact has 19 of them and the 15 outside the event path receive genuine
   class templates ([tfmap<List::list>]).  The rule is about what is being
   abstracted over.  See the [hkt-kind-demotion-dead-end] note.

   Three things have to hold together for the defect to appear at all, and
   each was a wrong turn on the way here.

   1. **The dictionary is skipped, not merely unused.**  Crane's ITree mapping
      has [Crane Extract Skip ReSum.] and [subevent => "%a0"], so the
      `` `{UBE -< E} `` parameter's type is erased and [E] loses its last
      occurrence in the emitted signature.  With an ordinary user class the
      parameter survives and an arity can be read off it -- that is the
      neighbouring test [subevent_forward_loses_kind], a different defect.

   2. **The callee keeps the higher kind only because its codomain is an
      itree.**  With [list B] as the result, `trigger_cast'` demotes on its
      own and the whole thing compiles.  Both earlier reduction attempts used
      [list B] and so could not reproduce this.

   3. **The event family must be index-based with constructors at differing
      indices.**  [UBE (A : Type)] comes out [template <typename A> struct UBE]
      -- a real template, which could satisfy the position, making the defect
      merely that the call spells [std::any] instead of [UBE].

   Demoting exposed a second defect underneath, fixed with it.  The
   continuation `fun x => void_elim x` eliminates an absurd response, so its
   own result type is a type variable and it returns [std::any]; the bind then
   had no tree type to be.  [itree_erased_bind_t] defers that to the use site,
   exactly as [itree_trigger_t] already defers the response type. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
Require Import List.

Inductive void : Set := .

(* Index, not parameter, and two constructors: emits a plain struct. *)
Inductive UBE : Type -> Type :=
| throwub : unit -> UBE void
| ubread  : unit -> UBE nat.

(* ITreeUtil.trigger_cast', verbatim: the family parameter is applied in the
   domain and named in the codomain, and the codomain drops it. *)
Definition void_elim {A} : void -> A := fun v => match v with end.

Definition trigger_cast' {E : Type -> Type} {A : Type} (e : E void)
  : itree E A := ITree.bind (ITree.trigger e) (fun x => void_elim x).

Module SkippedDictFamilyUnconstrained.
  (* LLVMEvents.raiseUB: the only occurrence of [E] is the subevent class,
     and that class is skipped. *)
  Definition raiseUB {E} `{UBE -< E} {X} : itree E X :=
    trigger_cast' (subevent _ (throwub tt)).

  Definition run : itree UBE nat := raiseUB.
End SkippedDictFamilyUnconstrained.

Crane Extraction "skipped_dict_family_unconstrained"
  SkippedDictFamilyUnconstrained.
