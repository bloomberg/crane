(** WIP test: spurious any_cast on concrete pair/deque fields.
    Same as sll_pair_cast but with DequeList mapping enabled.
    Crane generates any_cast<std::deque<std::any>>(l) where l is already
    a concrete std::deque<sll_frame>. Causes bad_any_cast at runtime.

    Reproduces parse-a-lot's SLLPrediction::sll_final_config crash
    when using Mapping.DequeList. *)
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.DequeList.
Require Crane.Extraction.

Module SllPairCastDeque.

(** A frame record with a concrete structure *)
Record sll_frame := sll_fr {
  fr_ret : option nat;
  fr_suf : list nat
}.

(** A stack: pair of frame and list of frames *)
Definition sll_stack := (sll_frame * list sll_frame)%type.

(** A subparser record with a stack field *)
Record sll_subparser := sll_sp {
  sll_pred : list nat;
  sll_stk  : sll_stack
}.

(** Deep pattern match on the record that destructures the pair inside.
    With DequeList, Crane generates:
      any_cast<pair<sll_frame, deque<sll_frame>>>(sll_stk0)
    where sll_stk0 is already the concrete pair type.
    Also generates:
      any_cast<deque<any>>(l)
    where l is already deque<sll_frame>. *)
Definition sll_final_config (sp : sll_subparser) : bool :=
  match sp with
  | sll_sp _ (sll_fr None [], []) => true
  | _ => false
  end.

(** Test values *)
Definition test_final : bool :=
  sll_final_config (sll_sp [1;2] (sll_fr None [], [])).

Definition test_not_final : bool :=
  sll_final_config (sll_sp [] (sll_fr (Some 5) [1], [sll_fr None []])).

End SllPairCastDeque.

Set Crane Loopify.
Crane Separate Extraction
  SllPairCastDeque.test_final
  SllPairCastDeque.test_not_final.
