(** Crane bug(s): combining two handlers with ITree's [case_] (the
    [Case Handler sum1] instance of ITree's handler category) does not
    compile.  An acceptance test: interpreting [A] then [B] with
    [case_ ha hb] must give 1 + 2 = 3.

    Layer seen on 0b2cfbbd5, in the emitted instance function:
      return Handler_Mod::template case_<std::any, std::any, std::any, std::any>(
          x, x0,
          std::any_cast<Sum1<std::any<std::any>, std::any<std::any>, std::any>>(x1));
    The category's objects are families; erased, each is [std::any], and an
    erased family applied at the index comes out as [std::any<std::any>]:
      error: expected '>'
      error: type name requires a specifier or qualifier
    (An erased family applied at anything should just be [std::any].)
    Behind it: [interp] needs [MonadIter_itree] (see itree_interp).

    Reduced from Vellvm, whose interpretation stack builds its handlers with
    [case_] / [bimap] / [id_] ([Semantics/InterpretationStack.v]); the same
    [std::any<std::any>] is Vellvm's first parse failure
    ([vellvm_bench.cpp:2259]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module ItreeCaseHandler.
  Variant aE : Type -> Type := A : aE nat.
  Variant bE : Type -> Type := B : bE nat.
  Variant noE : Type -> Type := .

  Definition ha : aE ~> itree noE := fun _ e => match e with A => Ret 1 end.
  Definition hb : bE ~> itree noE := fun _ e => match e with B => Ret 2 end.

  (* Vellvm's interpretation stack combines handlers with [case_] (and
     [bimap]/[id_]) from ITree's handler category. *)
  Definition h : aE +' bE ~> itree noE := case_ ha hb.

  Definition prog : itree (aE +' bE) nat :=
    Vis (inl1 A) (fun x => Vis (inr1 B) (fun y => Ret (x + y))).

  Definition out : itree noE nat := interp h prog.

  Fixpoint run (fuel : nat) (t : itree noE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  Definition is_three : bool := match run 100 out with Some n => Nat.eqb n 3 | None => false end.
End ItreeCaseHandler.

Crane Extraction "itree_case_handler" ItreeCaseHandler.
