From Stdlib Require Import Nat List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree.
Require Crane.Extraction.

Set Crane Loopify.

Inductive pureE : Type -> Type := .
Crane Extract Skip pureE.

Module LoopifyItreeSeq.

(** Tail-recursive countdown using erased ITree. In sequential mode, itree is
    erased so this becomes a plain tail-recursive C++ function. Loopify should
    convert it to a while loop. *)
Definition count_down (n : nat) : itree pureE nat :=
  (fix go (k : nat) (acc : nat) :=
    match k with
    | 0 => Ret acc
    | S k' => go k' (acc + 1)
    end) n 0.

(** Sum 1..n via tail recursion with accumulator. *)
Definition sum_to (n : nat) : itree pureE nat :=
  (fix go (k : nat) (acc : nat) :=
    match k with
    | 0 => Ret acc
    | S k' => go k' (acc + k)
    end) n 0.

(** Non-tail recursive: build a list counting down from n. *)
Fixpoint countdown_list (n : nat) : itree pureE (list nat) :=
  match n with
  | 0 => Ret (0 :: nil)
  | S n' => rest <- countdown_list n' ;; Ret (n :: rest)
  end.

(** Cofixpoint returning an erased ITree. In sequential mode, Tau is erased,
    so this becomes a plain tail-recursive C++ function:
    [delay_ret(n, v) { if (n==0) return v; else return delay_ret(n-1, v); }].
    Since itree is custom-extracted, [cofix_wrap] does not fire and there is no
    [lazy_] wrapper — the function is loopified normally as tail recursion. *)
CoFixpoint delay_ret (n : nat) (v : nat) : itree pureE nat :=
  match n with
  | 0 => Ret v
  | S n' => Tau (delay_ret n' v)
  end.

Definition test_count_5 := count_down 5.
Definition test_sum_10 := sum_to 10.
Definition test_clist_4 := countdown_list 4.
Definition test_delay := delay_ret 5 42.

End LoopifyItreeSeq.

Crane Extraction "loopify_itree_seq" LoopifyItreeSeq.
