(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.NatInt.NZOrder.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import State.

(** Concrete implementation of the prefix-scanning and rule-matching helpers. *)
Module ImplFn (Import ST : State.T).

  Import ST.Ty.
  Import ST.Defs.

  (* Invariant: index == length s *)
  (** Computes the maximal prefix of [s] accepted by [state], returning prefix, suffix, and updated index. *)
  Fixpoint max_pref_fn (s : String) (i : index) (state : State)
    : option (Prefix * Suffix * index):=
    match s with
    (* in a regex approach, accepting := nullable *)
    | [] => if accepting state then Some ([],[],i) else None
    | a :: s' =>
      let
        (* in a regex approach, transition := derivative *)
        state' := transition a state in
      let
        mpxs := max_pref_fn s' (decr i) state' in

      match mpxs with
      | None => if (accepting state') then Some ([a], s', (decr i)) else
                 if (accepting state) then Some ([], s, i) else
                   None
      | Some (p, q, qi) => Some (a :: p, q, qi)
      end
    end.

  (** Applies [max_pref_fn] to a single labelled FSM rule, pairing the label with its result. *)
  Definition extract_fsm_for_max (code : String) (i : index)
             (sru : (Label * State)) :=
    match sru with
      (a, fsm) => (a, max_pref_fn code i fsm)
    end.

  (** Maps [extract_fsm_for_max] over all rules to obtain per-rule maximal prefix candidates. *)
  Definition max_prefs (code : String) (i : index)
             (erules : list (Label * State))
    :=
      map (extract_fsm_for_max code i) erules.

  (* prefixes closest to the head are preferred *)
  (** Selects the longer of two labelled prefix candidates; ties favour the left (earlier) rule. *)
  Definition longer_pref (apref1 apref2 : Label * (option (Prefix * Suffix * index)))
    : Label * (option (Prefix * Suffix * index)) :=
    match apref1, apref2 with
    | (_, None), (_, _) => apref2
    | (_, _), (_, None) => apref1
    (* This is finding the min right now... *)
    | (_, Some (x, _, _)), (_, Some (y, _, _)) => if (length x) =? (length y)
                                                 then apref1 else
                                                   if (length x) <? (length y)
                                                   then apref2 else apref1
    end.


  (** Folds [longer_pref] over a list of candidates to find the overall maximal prefix. *)
  Fixpoint max_of_prefs (mprefs : list (Label * (option (Prefix * Suffix * index))))
    : Label * option (Prefix * Suffix * index) :=
    match mprefs with
    | [] => (defLabel, @None (String * String * index))
    | p :: ps => longer_pref p (max_of_prefs ps)
    end.

  (** Initialises a rule by converting its regex to the corresponding initial FSM state. *)
  Definition init_srule (rule : Rule) : sRule :=
    match rule with
    | (label, re) => (label, init_state re)
    end.


End ImplFn.
