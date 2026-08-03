From Stdlib Require Import Arith.PeanoNat List Arith.Wf_nat.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

Module LoopifyNontailPair.

Definition classify (l : list nat) : nat * option (nat * list nat) :=
  match l with
  | [] => (0, None)
  | x :: xs => (x, Some (x, xs))
  end.

Lemma classify_lt : forall (l : list nat) (t x : nat) (xs : list nat),
    classify l = (t, Some (x, xs)) -> length xs < length l.
Proof.
  intros [| y ys] t x xs Heq; simpl in Heq; inversion Heq; subst; simpl; auto.
Qed.

Fixpoint countdown (l : list nat) (Ha : Acc lt (length l)) {struct Ha}
  : nat * list nat * list nat :=
  match classify l as c return classify l = c -> _ with
  | (_, None) => fun _ => (O, [], l)
  | (_, Some (x, xs)) => fun Heq =>
      match countdown xs (Acc_inv Ha (classify_lt l _ x xs Heq)) with
      | (cnt, acc, rest) => (S cnt, x :: acc, rest)
      end
  end eq_refl.

Definition countdown_top (l : list nat) : nat * list nat * list nat :=
  countdown l (lt_wf (length l)).

Definition run_count (l : list nat) : nat := fst (fst (countdown_top l)).

End LoopifyNontailPair.

Crane Extraction "loopify_nontail_pair"
  LoopifyNontailPair.countdown
  LoopifyNontailPair.run_count.
