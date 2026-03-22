(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: coalition bidding, phase tracing, and honor updates over protocol state. *)

From Stdlib Require Import List Bool ZArith.
Import ListNotations.
Open Scope Z_scope.

Module CoalitionBidHonorTraceCase.

Inductive Clan : Type :=
| ClanWolf
| ClanJadeFalcon
| ClanGhostBear.

Definition clan_eq_dec : forall (c1 c2 : Clan), {c1 = c2} + {c1 <> c2}.
Proof. decide equality. Defined.

Definition clan_eqb (c1 c2 : Clan) : bool :=
  if clan_eq_dec c1 c2 then true else false.

Inductive Rank : Type :=
| Warrior
| StarCaptain
| StarColonel.

Definition rank_to_nat (r : Rank) : nat :=
  match r with
  | Warrior => 0
  | StarCaptain => 3
  | StarColonel => 4
  end.

Definition rank_le (r1 r2 : Rank) : bool :=
  Nat.leb (rank_to_nat r1) (rank_to_nat r2).

Record Commander : Type := mkCommander {
  cmd_id : nat;
  cmd_clan : Clan;
  cmd_rank : Rank;
  cmd_bloodnamed : bool
}.

Definition may_issue_batchall (c : Commander) : bool :=
  rank_le StarCaptain (cmd_rank c).

Inductive UnitClass : Type :=
| OmniMech
| BattleMech
| Elemental.

Inductive WeightClass : Type :=
| Light
| Heavy
| Assault.

Definition weight_class_value (w : WeightClass) : nat :=
  match w with
  | Light => 10
  | Heavy => 15
  | Assault => 18
  end.

Definition unit_class_bonus (c : UnitClass) : nat :=
  match c with
  | OmniMech => 20
  | BattleMech => 10
  | Elemental => 15
  end.

Record Unit : Type := mkUnit {
  unit_id : nat;
  unit_class : UnitClass;
  unit_weight : WeightClass;
  unit_tonnage : nat;
  unit_gunnery : nat;
  unit_piloting : nat;
  unit_is_elite : bool;
  unit_is_clan : bool
}.

Definition unit_skill (u : Unit) : nat :=
  unit_gunnery u + unit_piloting u.

Definition skill_bv_multiplier_num (skill : nat) : nat :=
  if Nat.leb skill 4 then 6
  else if Nat.leb skill 6 then 5
  else if Nat.leb skill 8 then 4
  else 3.

Definition unit_base_bv (u : Unit) : nat :=
  unit_tonnage u * weight_class_value (unit_weight u).

Definition unit_tech_bv (u : Unit) : nat :=
  let base := unit_base_bv u in
  if unit_is_clan u then base + base / 2 else base.

Definition unit_battle_value (u : Unit) : nat :=
  let tech_bv := unit_tech_bv u in
  (tech_bv * skill_bv_multiplier_num (unit_skill u)) / 4.

Definition unit_effective_combat_rating (u : Unit) : nat :=
  unit_battle_value u + unit_class_bonus (unit_class u).

Definition Force : Type := list Unit.

Record ForceMetrics : Type := mkForceMetrics {
  fm_count : nat;
  fm_tonnage : nat;
  fm_elite_count : nat;
  fm_clan_count : nat;
  fm_total_bv : nat;
  fm_total_ecr : nat
}.

Definition empty_metrics : ForceMetrics :=
  mkForceMetrics 0 0 0 0 0 0.

Definition unit_to_metrics (u : Unit) : ForceMetrics :=
  mkForceMetrics
    1
    (unit_tonnage u)
    (if unit_is_elite u then 1 else 0)
    (if unit_is_clan u then 1 else 0)
    (unit_battle_value u)
    (unit_effective_combat_rating u).

Definition metrics_add (m1 m2 : ForceMetrics) : ForceMetrics :=
  mkForceMetrics
    (fm_count m1 + fm_count m2)
    (fm_tonnage m1 + fm_tonnage m2)
    (fm_elite_count m1 + fm_elite_count m2)
    (fm_clan_count m1 + fm_clan_count m2)
    (fm_total_bv m1 + fm_total_bv m2)
    (fm_total_ecr m1 + fm_total_ecr m2).

Definition force_metrics (f : Force) : ForceMetrics :=
  fold_right (fun u acc => metrics_add (unit_to_metrics u) acc) empty_metrics f.

Definition metrics_total_lt (m1 m2 : ForceMetrics) : bool :=
  Nat.ltb (fm_total_ecr m1) (fm_total_ecr m2).

Inductive Side : Type :=
| Attacker
| Defender.

Record CoalitionMember : Type := mkCoalitionMember {
  cm_clan : Clan;
  cm_commander : Commander;
  cm_force : Force
}.

Definition Coalition : Type := list CoalitionMember.

Definition coalition_force (c : Coalition) : Force :=
  flat_map cm_force c.

Definition coalition_metrics (c : Coalition) : ForceMetrics :=
  force_metrics (coalition_force c).

Definition coalition_contains_clan (c : Coalition) (clan : Clan) : bool :=
  existsb (fun m => clan_eqb (cm_clan m) clan) c.

Definition coalition_tonnage (c : Coalition) : nat :=
  fm_tonnage (coalition_metrics c).

Record CoalitionMemberBid : Type := mkCoalitionMemberBid {
  cmb_member_index : nat;
  cmb_new_force : Force;
  cmb_side : Side
}.

Fixpoint update_coalition_force
    (c : Coalition)
    (idx : nat)
    (new_force : Force)
    : Coalition :=
  match c, idx with
  | [], _ => []
  | m :: rest, O =>
      mkCoalitionMember (cm_clan m) (cm_commander m) new_force :: rest
  | m :: rest, S n =>
      m :: update_coalition_force rest n new_force
  end.

Record ForceBid : Type := mkForceBid {
  bid_force : Force;
  bid_side : Side;
  bid_commander : Commander
}.

Definition bid_metrics (b : ForceBid) : ForceMetrics :=
  force_metrics (bid_force b).

Definition coalition_lead_commander (c : Coalition) : option Commander :=
  match c with
  | [] => None
  | m :: _ => Some (cm_commander m)
  end.

Definition coalition_to_bid (c : Coalition) (side : Side) : option ForceBid :=
  match coalition_lead_commander c with
  | None => None
  | Some cmd => Some (mkForceBid (coalition_force c) side cmd)
  end.

Definition apply_coalition_member_bid
    (c : Coalition)
    (cbid : CoalitionMemberBid)
    : Coalition :=
  update_coalition_force c (cmb_member_index cbid) (cmb_new_force cbid).

Definition valid_coalition_member_bid_b
    (c : Coalition)
    (cbid : CoalitionMemberBid)
    : bool :=
  Nat.ltb (cmb_member_index cbid) (length c) &&
  metrics_total_lt
    (force_metrics (cmb_new_force cbid))
    (force_metrics (nth (cmb_member_index cbid) (map cm_force c) [])).

Inductive TrialType : Type :=
| TrialOfPossession
| TrialOfAnnihilation.

Inductive Prize : Type :=
| PrizeHonor
| PrizeEnclave (enclave_id : nat).

Inductive Location : Type :=
| LocPlanetSurface (world_id : nat) (region_id : nat)
| LocEnclave (enclave_id : nat).

Record BattleContext : Type := mkBattleContext {
  ctx_hegira_allowed : bool;
  ctx_circle_present : bool
}.

Definition standard_possession_context : BattleContext :=
  mkBattleContext true false.

Record BatchallChallenge : Type := mkBatchallChallenge {
  chal_challenger : Commander;
  chal_clan : Clan;
  chal_prize : Prize;
  chal_initial_force : Force;
  chal_location : Location;
  chal_trial_type : TrialType;
  chal_context : BattleContext
}.

Record BatchallResponse : Type := mkBatchallResponse {
  resp_defender : Commander;
  resp_clan : Clan;
  resp_force : Force
}.

Inductive RefusalReason : Type :=
| RefusalInsufficientRank
| RefusalOther (note : nat).

Inductive ProtocolAction : Type :=
| ActChallenge (chal : BatchallChallenge)
| ActRespond (resp : BatchallResponse)
| ActRefuse (reason : RefusalReason)
| ActBid (bid : ForceBid)
| ActCoalitionBid (cbid : CoalitionMemberBid)
| ActPass (side : Side)
| ActClose
| ActWithdraw (side : Side)
| ActBreakBid (side : Side).

Inductive ReadyStatus : Type :=
| NeitherReady
| AttackerReady
| DefenderReady
| BothReady.

Definition is_ready (rs : ReadyStatus) (side : Side) : bool :=
  match rs, side with
  | AttackerReady, Attacker => true
  | DefenderReady, Defender => true
  | BothReady, _ => true
  | _, _ => false
  end.

Definition set_ready (rs : ReadyStatus) (side : Side) : ReadyStatus :=
  match rs, side with
  | NeitherReady, Attacker => AttackerReady
  | NeitherReady, Defender => DefenderReady
  | AttackerReady, Defender => BothReady
  | DefenderReady, Attacker => BothReady
  | _, _ => rs
  end.

Definition clear_ready (rs : ReadyStatus) (side : Side) : ReadyStatus :=
  match rs, side with
  | AttackerReady, Attacker => NeitherReady
  | DefenderReady, Defender => NeitherReady
  | BothReady, Attacker => DefenderReady
  | BothReady, Defender => AttackerReady
  | _, _ => rs
  end.

Definition CoalitionState : Type := option Coalition.

Definition coalition_state_force (cs : CoalitionState) (fallback : Force) : Force :=
  match cs with
  | None => fallback
  | Some c => coalition_force c
  end.

Inductive BatchallPhase : Type :=
| PhaseIdle
| PhaseChallenged (challenge : BatchallChallenge)
| PhaseResponded (challenge : BatchallChallenge) (response : BatchallResponse)
| PhaseBidding (challenge : BatchallChallenge) (response : BatchallResponse)
               (attacker_bid : ForceBid) (defender_bid : ForceBid)
               (attacker_coalition : CoalitionState) (defender_coalition : CoalitionState)
               (bid_history : list ForceBid) (ready : ReadyStatus)
| PhaseAgreed (challenge : BatchallChallenge) (response : BatchallResponse)
              (final_attacker : ForceBid) (final_defender : ForceBid)
| PhaseRefused (challenge : BatchallChallenge) (reason : RefusalReason)
| PhaseAborted (reason : ProtocolAction).

Definition is_terminal (phase : BatchallPhase) : bool :=
  match phase with
  | PhaseAgreed _ _ _ _ => true
  | PhaseRefused _ _ => true
  | PhaseAborted _ => true
  | _ => false
  end.

Definition is_bidding (phase : BatchallPhase) : bool :=
  match phase with
  | PhaseBidding _ _ _ _ _ _ _ _ => true
  | _ => false
  end.

Definition phase_depth (phase : BatchallPhase) : nat :=
  match phase with
  | PhaseIdle => 4
  | PhaseChallenged _ => 3
  | PhaseResponded _ _ => 2
  | PhaseBidding _ _ _ _ _ _ _ _ => 1
  | PhaseAgreed _ _ _ _ => 0
  | PhaseRefused _ _ => 0
  | PhaseAborted _ => 0
  end.

Definition get_bidding_measure (phase : BatchallPhase) : nat :=
  match phase with
  | PhaseBidding _ _ atk def _ _ _ ready =>
      fm_total_ecr (bid_metrics atk) +
      fm_total_ecr (bid_metrics def) +
      match ready with
      | NeitherReady => 2
      | AttackerReady => 1
      | DefenderReady => 1
      | BothReady => 0
      end
  | _ => 0
  end.

Definition Honor : Type := Z.
Definition HonorEntry : Type := (nat * Honor)%type.
Definition HonorLedger : Type := list HonorEntry.

Fixpoint ledger_lookup (ledger : HonorLedger) (warrior_id : nat) : Honor :=
  match ledger with
  | [] => 0
  | (id, honor) :: rest =>
      if Nat.eqb id warrior_id then honor else ledger_lookup rest warrior_id
  end.

Fixpoint ledger_update_by_id
    (ledger : HonorLedger)
    (warrior_id : nat)
    (new_honor : Honor)
    : HonorLedger :=
  match ledger with
  | [] => [(warrior_id, new_honor)]
  | (id, honor) :: rest =>
      if Nat.eqb id warrior_id
      then (id, new_honor) :: rest
      else (id, honor) :: ledger_update_by_id rest warrior_id new_honor
  end.

Definition update_honor
    (ledger : HonorLedger)
    (actor : Commander)
    (delta : Honor)
    : HonorLedger :=
  let current := ledger_lookup ledger (cmd_id actor) in
  ledger_update_by_id ledger (cmd_id actor) (current + delta).

Definition refusal_honor_delta (r : RefusalReason) : Honor :=
  match r with
  | RefusalInsufficientRank => 0
  | RefusalOther _ => -1
  end.

Definition protocol_honor_delta (action : ProtocolAction) : Honor :=
  match action with
  | ActChallenge _ => 1
  | ActRespond _ => 1
  | ActRefuse reason => refusal_honor_delta reason
  | ActBid _ => 0
  | ActCoalitionBid _ => 0
  | ActPass _ => 0
  | ActClose => 1
  | ActWithdraw _ => -2
  | ActBreakBid _ => -10
  end.

Definition get_side_commander (phase : BatchallPhase) (side : Side) : option Commander :=
  match phase with
  | PhaseBidding _ _ atk def _ _ _ _ =>
      match side with
      | Attacker => Some (bid_commander atk)
      | Defender => Some (bid_commander def)
      end
  | _ => None
  end.

Definition action_actor_in_phase (phase : BatchallPhase) (action : ProtocolAction)
    : option Commander :=
  match action with
  | ActChallenge chal => Some (chal_challenger chal)
  | ActRespond resp => Some (resp_defender resp)
  | ActRefuse _ => None
  | ActBid bid => Some (bid_commander bid)
  | ActCoalitionBid _ => None
  | ActPass _ => None
  | ActClose => None
  | ActWithdraw side => get_side_commander phase side
  | ActBreakBid side => get_side_commander phase side
  end.

Record BatchallState : Type := mkBatchallState {
  bs_phase : BatchallPhase;
  bs_honor : HonorLedger
}.

Definition empty_ledger : HonorLedger := [].

Definition initial_state : BatchallState :=
  mkBatchallState PhaseIdle empty_ledger.

Definition apply_action_honor (state : BatchallState) (action : ProtocolAction) : HonorLedger :=
  match action_actor_in_phase (bs_phase state) action with
  | Some actor => update_honor (bs_honor state) actor (protocol_honor_delta action)
  | None => bs_honor state
  end.

Definition malthus : Commander :=
  mkCommander 1 ClanJadeFalcon StarColonel true.

Definition radick : Commander :=
  mkCommander 2 ClanWolf StarCaptain true.

Definition bear_ally : Commander :=
  mkCommander 3 ClanGhostBear StarCaptain false.

Definition timberwolf : Unit :=
  mkUnit 101 OmniMech Heavy 75 2 3 true true.

Definition direwolf : Unit :=
  mkUnit 102 OmniMech Assault 100 2 3 true true.

Definition summoner : Unit :=
  mkUnit 103 OmniMech Heavy 70 3 4 false true.

Definition mad_dog : Unit :=
  mkUnit 104 OmniMech Heavy 60 3 4 false true.

Definition elementals : Unit :=
  mkUnit 105 Elemental Light 5 3 4 false true.

Definition falcon_trinary : Force :=
  [direwolf; timberwolf; summoner; mad_dog].

Definition wolf_binary : Force :=
  [timberwolf; summoner].

Definition bear_support : Force :=
  [elementals; elementals].

Definition attacker_coalition : Coalition :=
  [ mkCoalitionMember ClanJadeFalcon malthus falcon_trinary;
    mkCoalitionMember ClanGhostBear bear_ally bear_support ].

Definition defender_coalition : Coalition :=
  [ mkCoalitionMember ClanWolf radick wolf_binary ].

Definition sample_challenge : BatchallChallenge :=
  mkBatchallChallenge
    malthus
    ClanJadeFalcon
    (PrizeEnclave 42)
    (coalition_force attacker_coalition)
    (LocPlanetSurface 7 3)
    TrialOfPossession
    standard_possession_context.

Definition sample_response : BatchallResponse :=
  mkBatchallResponse
    radick
    ClanWolf
    (coalition_force defender_coalition).

Definition sample_attacker_bid : ForceBid :=
  match coalition_to_bid attacker_coalition Attacker with
  | Some bid => bid
  | None => mkForceBid [] Attacker malthus
  end.

Definition sample_defender_bid : ForceBid :=
  match coalition_to_bid defender_coalition Defender with
  | Some bid => bid
  | None => mkForceBid [] Defender radick
  end.

Definition reduced_support_force : Force := [elementals].

Definition sample_coalition_member_bid : CoalitionMemberBid :=
  mkCoalitionMemberBid 1 reduced_support_force Attacker.

Definition updated_attacker_coalition : Coalition :=
  apply_coalition_member_bid attacker_coalition sample_coalition_member_bid.

Definition updated_attacker_bid : ForceBid :=
  match coalition_to_bid updated_attacker_coalition Attacker with
  | Some bid => bid
  | None => sample_attacker_bid
  end.

Definition phase_after_initial_bid : BatchallPhase :=
  PhaseBidding sample_challenge sample_response
    sample_attacker_bid sample_defender_bid
    (Some attacker_coalition) (Some defender_coalition)
    [] NeitherReady.

Definition phase_after_attacker_pass : BatchallPhase :=
  PhaseBidding sample_challenge sample_response
    sample_attacker_bid sample_defender_bid
    (Some attacker_coalition) (Some defender_coalition)
    [] AttackerReady.

Definition phase_after_coalition_bid : BatchallPhase :=
  PhaseBidding sample_challenge sample_response
    updated_attacker_bid sample_defender_bid
    (Some updated_attacker_coalition) (Some defender_coalition)
    [sample_attacker_bid] NeitherReady.

Definition phase_agreed : BatchallPhase :=
  PhaseAgreed sample_challenge sample_response
    updated_attacker_bid sample_defender_bid.

Definition state_after_initial_bid : BatchallState :=
  mkBatchallState phase_after_initial_bid empty_ledger.

Definition sample_challenge_honor_ledger : HonorLedger :=
  apply_action_honor initial_state (ActChallenge sample_challenge).

Definition sample_break_bid_honor_ledger : HonorLedger :=
  apply_action_honor state_after_initial_bid (ActBreakBid Attacker).

Definition sample_challenger_may_issue : bool :=
  may_issue_batchall malthus.

Definition sample_coalition_bid_is_valid : bool :=
  valid_coalition_member_bid_b attacker_coalition sample_coalition_member_bid.

Definition sample_coalition_contains_bear : bool :=
  coalition_contains_clan attacker_coalition ClanGhostBear.

Definition sample_updated_tonnage_reduced : bool :=
  Nat.ltb (coalition_tonnage updated_attacker_coalition)
    (coalition_tonnage attacker_coalition).

Definition sample_attacker_ready_after_pass : bool :=
  is_ready (set_ready NeitherReady Attacker) Attacker.

Definition sample_attacker_not_ready_after_clear : bool :=
  negb (is_ready (clear_ready BothReady Attacker) Attacker).

Definition sample_phase_is_bidding : bool :=
  is_bidding phase_after_initial_bid.

Definition sample_agreed_terminal : bool :=
  is_terminal phase_agreed.

Definition sample_phase_depth_before_close : nat :=
  phase_depth phase_after_initial_bid.

Definition sample_phase_depth_after_close : nat :=
  phase_depth phase_agreed.

Definition sample_bidding_measure_reduced : bool :=
  Nat.ltb (get_bidding_measure phase_after_coalition_bid)
    (get_bidding_measure phase_after_initial_bid).

Definition sample_challenge_honor : Honor :=
  ledger_lookup sample_challenge_honor_ledger (cmd_id malthus).

Definition sample_break_bid_honor : Honor :=
  ledger_lookup sample_break_bid_honor_ledger (cmd_id malthus).

Definition sample_challenge_honor_is_one : bool :=
  Z.eqb sample_challenge_honor 1.

Definition sample_break_bid_honor_is_minus_ten : bool :=
  Z.eqb sample_break_bid_honor (-10).

Definition sample_break_bid_actor_id : nat :=
  match action_actor_in_phase phase_after_initial_bid (ActBreakBid Attacker) with
  | Some cmd => cmd_id cmd
  | None => 0
  end.

Definition sample_attacker_bid_count : nat :=
  fm_count (bid_metrics sample_attacker_bid).

Definition sample_updated_bid_count : nat :=
  fm_count (bid_metrics updated_attacker_bid).

Definition sample_state_force_count : nat :=
  length (coalition_state_force (Some attacker_coalition) []).

End CoalitionBidHonorTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "coalition_bid_honor_trace" CoalitionBidHonorTraceCase.
