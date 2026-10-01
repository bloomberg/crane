(* [itree E unit] is [shared_ptr<ITree<std::monostate>>] -- never [void].

   Void-ification is the rule that a computation with nothing to give back is a
   *statement*: [f : IO unit] becomes [void f()].  That is true of the
   sequential backend, where the computation is the call.  Under the reified
   backend the computation is *data* -- a tree that has to be returned, built,
   and bound into -- and Rocq's [unit] is inhabited, so the tree carries a
   value.  Applying void-ification there does not change a type, it deletes a
   term.

   The predicate behind it is [ml_result_type], which reaches into a monad's
   last type argument, so [itree E unit] reports result type [unit].  It was
   re-implemented at roughly eight sites.  All eight agreed on the predicate
   and differed on the *consequence*, which is why each site was internally
   consistent and the file as a whole had four spellings of one Rocq type:

     static void                          put(Nat n);      // itree E unit
     static void                          both(bool b);    // itree E unit
     static std::shared_ptr<ITree<void>>  prog();          // itree E unit

   plus [std::monostate] wherever a unit result was synthesised.

   [put] is the part to look at twice.  It came out as

     void put(Nat n) { itree_trigger(E::put(std::move(n))); return; }

   -- the tree that [trigger] builds is constructed and dropped.  No cast fixes
   that: a program sequenced through these calls has had its sequencing thrown
   away.  The compile errors were the lucky part; had [unit] been erased
   consistently this would have built and run wrong.  So the instrument for
   this class of defect is not the error count.

   [both] is the minimal shape: one match, both branches of Rocq type
   [itree E unit], one a trigger and one a [Ret], previously emitted as a
   [void] call against an [itree_ret(std::monostate{})].

   The fix is one shared predicate, [Translation.ml_type_is_void_call], which
   adds [not (codomain_is_reified_monad ty)], with [apply_unit_void] for the
   consequence.  Two things it must keep doing:

   - An *inline custom* stays void-ified on purpose.  [print]'s replacement
     text is [std::cout << s << '\n'] -- a statement -- whatever its Rocq type
     says, and being void-ified is what makes the call site wrap it in a
     tree-returning IIFE.  The text, not the type, says what the C++ yields.
   - [Ret tt] spells [ITree<Unit>::ret(std::monostate{})], not [ITree<void>].

   Vellvm: this was 4 of the 27 remaining errors, all "void block should not
   return a value", in [Denotation]'s instruction handler. *)

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
