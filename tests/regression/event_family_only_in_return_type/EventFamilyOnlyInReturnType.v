(* Why the event family is spelled [std::any] at a call that could name it,
   and why that is the right spelling rather than a defect.

     template <typename T1 = void, typename T2>
     static std::shared_ptr<ITree<T2>> raiseUB() {
       return trigger_cast_<std::any, T2>(UBE::throwub(std::monostate{}));
     }

   This is Vellvm's [raiseUB] token for token, and reading it as an erasure
   bug is the natural reading: [T1] is declared, the caller writes it
   ([raiseUB<UBE, Nat>()]), and the body could have said [T1].  It could not.

   [subevent] is mapped away -- [Monads/ITreeBase.v] has [Crane Extract Skip
   ReSum] and [subevent => "%a0"] -- so the injection is erased to its
   argument and the value the body passes is a bare [UBE], whatever family
   the caller is working in.  [trigger_cast_]'s parameter is that value's
   type.  Writing the family there would type the parameter at the family and
   the argument at [UBE], and the two only coincide when the family is [UBE]
   itself.  [run_sum] here is the witness: at [UBE +' OOME] the call comes out
   [raiseUB<void, Nat>()], because a sum family is not spelled in C++ at all.
   [std::any] is the one spelling that accepts the base event under every
   family, and [default_unmentioned_temps] is what puts it there -- [T1] is
   mentioned in no part of [raiseUB]'s own signature, so its body occurrences
   are erased with it.

   Nor does the erasure cost anything at run time.  The event is boxed once,
   not twice: [itree_trigger] reifies it as a thunk yielding [std::any], and
   [std::any(std::any)] is a copy rather than a nesting, so the box holds the
   [UBE] and [crane_event_as<UBE>] recovers it.  That is what this test
   asserts, at both families -- the oracle is the recovered event, since
   nothing here fails to compile and the counts a diagnostic would move are
   all zero either way.

   What the shape does cost is a lost check: the position that should say
   which family the tree is over says nothing, so a handler at the wrong
   family is a run-time [bad_any_cast] rather than a compile error.  Pinning
   the behaviour is the point of keeping the test.

   Two conditions produce the shape, and five earlier reduction attempts
   (recorded on [subevent_forward_loses_kind]) missed by satisfying one.

   1. [E] occurs only in the return type and the constraint.  Give [raiseUB]
      any parameter mentioning [E] -- an [(e : E vd)] hint it ignores -- and
      [E] is mentioned in the signature, so it is no longer defaulted away.
   2. The constraint is ITree's real [-<].  With a hand-rolled class the
      dictionary parameter survives, an arity can be read off it, and what
      comes out is the mirror defect instead --- that is the neighbouring
      [subevent_forward_loses_kind].

   See also [skipped_dict_family_unconstrained], which is the callee half of
   the same shape: [trigger_cast_]'s own parameter, demoted from
   [template <typename> class] to [typename], which is what makes [std::any]
   a legal argument here. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

(* The event's index, empty, with its eliminator: LLVMEvents' [void]. *)
Inductive vd : Set := .
Definition vd_elim {A : Type} : vd -> A := fun v => match v with end.

Variant OOME : Type -> Type := throwoom : unit -> OOME vd.

Inductive UBE : Type -> Type :=
| throwub : unit -> UBE vd
| ubread : unit -> UBE nat.

(* ITreeUtil.trigger_cast', verbatim in shape: the argument is at the empty
   index and the continuation eliminates it, so [E] reaches the callee
   through the argument's type and [A] only through the result's. *)
Definition trigger_cast' {E : Type -> Type} {A : Type} (e : E vd) : itree E A :=
  ITree.bind (ITree.trigger e) vd_elim.

Module EventFamilyOnlyInReturnType.
  (* LLVMEvents.raiseUB: [E] is in the constraint and the result, nowhere
     else, and the constraint is erased. *)
  Definition raiseUB {E : Type -> Type} `{UBE -< E} {X : Type} : itree E X :=
    trigger_cast' (subevent _ (throwub tt)).

  Definition run : itree UBE nat := raiseUB.

  (* The same [raiseUB], at a larger family.  [subevent] is erased, so the
     value the call passes is still a bare [UBE] -- which is why the family
     position cannot be written as the family. *)
  Definition run_sum : itree (UBE +' OOME) nat := raiseUB.
End EventFamilyOnlyInReturnType.

Crane Extraction "event_family_only_in_return_type"
  EventFamilyOnlyInReturnType.
