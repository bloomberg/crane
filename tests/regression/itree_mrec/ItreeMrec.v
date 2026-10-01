(** Crane bug(s): ITree's [mrec] (Vellvm's [denote_mcfg] recursion over
    [CallE]) does not compile under vanilla extraction.  An acceptance test
    for the feature: it runs [sum_to 4] through [mrec] and checks 10.

    Layers seen on 2d01630ed:
    1. [mrec : (D ~> itree (D +' E)) -> D ~> itree E] is declared with [D]
       higher-kinded, [Itree<T2, T3> Recursion::mrec(F0 &&ctx, T1<T3> d)],
       while the call passes the family as a plain type:
         Recursion::template mrec<ItreeMrec::callE, ItreeMrec::noE, Nat>(...)
         error: no matching function for call to 'mrec'
         note: candidate template ignored: invalid explicitly-specified
               argument for template parameter 'T1'
       [D T] is [D] applied at the [forall T] of [~>], a variable, so by the
       2d01630ed rule [D] should be a plain family ([T1 d]).
    2. [trigger (Call k)] inside the handler goes through [subevent] /
       [ReSum IFun]; see itree_trigger_subevent (IFun, ReSum errors).

    Reduced from Vellvm, [Semantics/Denotation.v] [denote_mcfg]:
    [mrec (fun T call => ...) (Call dt f_value args)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module ItreeMrec.
  Variant callE : Type -> Type := Call : nat -> callE nat.
  Variant noE : Type -> Type := .

  (* Vellvm's denote_mcfg: mrec over a call event. Sum to n by recursion. *)
  Definition body : callE ~> itree (callE +' noE) :=
    fun _ e => match e with
               | Call O => Ret 0
               | Call (S k) => r <- trigger (Call k) ;; Ret (S k + r)
               end.

  Definition sum_to (n : nat) : itree noE nat := mrec body (Call n).

  Fixpoint run (fuel : nat) (t : itree noE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  Definition is_ten : bool := match run 1000 (sum_to 4) with Some n => Nat.eqb n 10 | None => false end.
End ItreeMrec.

Crane Extraction "itree_mrec" ItreeMrec.
