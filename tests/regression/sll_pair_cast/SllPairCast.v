(** WIP test: spurious any_cast on concrete pair fields.
    Reproduces the crash in parse-a-lot's SLLPrediction.sll_final_config,
    where Crane wraps a concrete pair<frame, list<frame>> in std::any
    then casts to pair<any,any>, causing bad_any_cast at runtime.
    
    The key pattern: a Record with a field of type (A * list A),
    destructured via a nested match on the record constructor. *)
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Require Crane.Extraction.

Module SllPairCast.

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

(** This is the problematic function: deep pattern match on the record
    that destructures the pair inside. *)
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

End SllPairCast.

Set Crane Loopify.
Crane Separate Extraction
  SllPairCast.test_final
  SllPairCast.test_not_final.
