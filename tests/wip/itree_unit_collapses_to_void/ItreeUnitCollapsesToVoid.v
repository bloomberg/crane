(* Expected: compiles.
   Actual:   error: no viable conversion from 'std::shared_ptr<ITree<Nat>>' to 'Nat'
             error: no viable conversion from ... 'std::monostate' to function
                    return type 'std::shared_ptr<ITree<void>>'
             error: no type named 'element_type' in 'std::monostate'

   Under the reified ITree backend, [itree E unit] gets three different C++
   spellings, and they meet.  In this one file:

     static void                          put(Nat n);      // itree E unit
     static void                          both(bool b);    // itree E unit
     static std::shared_ptr<ITree<void>>  prog();          // itree E unit

   and the value side adds a fourth, [std::monostate], wherever a unit result
   is synthesised.  [prog]'s continuation returns [std::monostate{}] into a
   declared [std::shared_ptr<ITree<void>>].

   The rule that produces this looks like [unit -> void] applied underneath the
   [itree] constructor rather than only at the top: [itree E dvalue] keeps its
   wrapper and becomes [shared_ptr<ITree<Dvalue>>], but [itree E unit] loses it
   and becomes plain [void].  [prog] escapes because its own return type is
   spelled from the tree, giving the uninhabited-looking [ITree<void>].

   The emitted [put] is the part to look at twice:

     void put(Nat n) { itree_trigger(E::put(std::move(n))); return; }

   The tree that [trigger] builds is constructed and dropped.  That is not a
   typing artefact that a cast would fix -- a program whose effects are
   sequenced through these calls has had the sequencing thrown away.  So this
   is worth treating as a soundness bug in the backend rather than as four
   compile errors, and the compile errors are the lucky part: had [unit] been
   erased consistently, this would have built and run wrong.

   [both] shows the two spellings colliding inside one match, which is the
   minimal shape: both branches have Rocq type [itree E unit], one is a
   trigger and one is a [Ret], and they come out as a [void] call and an
   [itree_ret(std::monostate{})] respectively.

   Vellvm: 4 of the 27 remaining errors, all "void block should not return a
   value", in [Denotation]'s instruction handler -- the [INSTR_Store] and
   [IId]/[IVoid] branches, where [LLVMEvents::store] and [LLVMEvents::lwrite]
   are both declared [void] while the surrounding [bind] is instantiated at
   [std::monostate] and a sibling branch returns
   [Monad_itree<std::any>::ret<std::monostate>(...)].  There
   [LLVMEvents::raiseUB] is a third spelling again, [shared_ptr<ITree<T2>>].
   vellvm_bench.h:18791, :18795, :19035, :19037. *)

From Crane Require Import Mapping.Std Monads.ITreeReified.
From Crane Require Extraction.
From ITree Require Import ITree.

Variant E : Type -> Type :=
  | Get : E nat
  | Put : nat -> E unit.

Module ItreeUnitCollapsesToVoid.

  Definition get : itree E nat  := ITree.trigger Get.
  Definition put (n : nat) : itree E unit := ITree.trigger (Put n).

  (* A match whose branches are both [itree E unit], one a trigger and one a
     [ret].  They should have one C++ type. *)
  Definition both (b : bool) : itree E unit :=
    match b with
    | true  => put 1
    | false => Ret tt
    end.

  Definition prog : itree E unit :=
    n <- get ;; both (Nat.eqb n 0).

End ItreeUnitCollapsesToVoid.

Crane Extraction "itree_unit_collapses_to_void" ItreeUnitCollapsesToVoid.
