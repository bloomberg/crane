#include <coalition_bid_honor_trace.h>

__attribute__((pure)) Positive Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*(d_a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(*(d_a0));
  } else {
    return Positive::xo(Positive::xh());
  }
}

__attribute__((pure)) Positive Pos::add(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*(d_a0), *(d_a00)));
    } else {
      return Positive::xo(succ(*(d_a0)));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add(*(d_a0), *(d_a00)));
    } else {
      return Positive::xi(*(d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(succ(*(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(*(d_a00));
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

__attribute__((pure)) Positive Pos::add_carry(const Positive &x,
                                              const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add_carry(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add_carry(*(d_a0), *(d_a00)));
    } else {
      return Positive::xi(succ(*(d_a0)));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*(d_a0), *(d_a00)));
    } else {
      return Positive::xo(succ(*(d_a0)));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(succ(*(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(succ(*(d_a00)));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

__attribute__((pure)) Positive Pos::pred_double(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xi(Positive::xo(*(d_a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(pred_double(*(d_a0)));
  } else {
    return Positive::xh();
  }
}

__attribute__((pure)) bool Pos::eqb(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(q.v());
      return eqb(*(d_a0), *(d_a00));
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(q.v());
      return eqb(*(d_a0), *(d_a00));
    } else {
      return false;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(q.v())) {
      return true;
    } else {
      return false;
    }
  }
}

__attribute__((pure)) Z BinInt::double_(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xo(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xo(d_a0));
  }
}

__attribute__((pure)) Z BinInt::succ_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xi(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Pos::pred_double(d_a0));
  }
}

__attribute__((pure)) Z BinInt::pred_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zneg(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Pos::pred_double(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xi(d_a0));
  }
}

__attribute__((pure)) Z BinInt::pos_sub(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return BinInt::double_(BinInt::pos_sub(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return BinInt::succ_double(BinInt::pos_sub(*(d_a0), *(d_a00)));
    } else {
      return Z::zpos(Positive::xo(*(d_a0)));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return BinInt::pred_double(BinInt::pos_sub(*(d_a0), *(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return BinInt::double_(BinInt::pos_sub(*(d_a0), *(d_a00)));
    } else {
      return Z::zpos(Pos::pred_double(*(d_a0)));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return Z::zneg(Positive::xo(*(d_a00)));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return Z::zneg(Pos::pred_double(*(d_a00)));
    } else {
      return Z::z0();
    }
  }
}

__attribute__((pure)) Z BinInt::add(Z x, Z y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::add(d_a0, d_a00));
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return BinInt::pos_sub(d_a0, d_a00);
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return BinInt::pos_sub(d_a00, d_a0);
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::add(d_a0, d_a00));
    }
  }
}

__attribute__((pure)) bool BinInt::eqb(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::eqb(d_a0, d_a00);
    } else {
      return false;
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return Pos::eqb(d_a0, d_a00);
    } else {
      return false;
    }
  }
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::clan_eq_dec(
    const CoalitionBidHonorTraceCase::Clan c1,
    const CoalitionBidHonorTraceCase::Clan c2) {
  switch (c1) {
  case Clan::e_CLANWOLF: {
    switch (c2) {
    case Clan::e_CLANWOLF: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case Clan::e_CLANJADEFALCON: {
    switch (c2) {
    case Clan::e_CLANJADEFALCON: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case Clan::e_CLANGHOSTBEAR: {
    switch (c2) {
    case Clan::e_CLANGHOSTBEAR: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::clan_eqb(
    const CoalitionBidHonorTraceCase::Clan c1,
    const CoalitionBidHonorTraceCase::Clan c2) {
  if (clan_eq_dec(c1, c2)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::rank_to_nat(
    const CoalitionBidHonorTraceCase::Rank r) {
  switch (r) {
  case Rank::e_WARRIOR: {
    return 0u;
  }
  case Rank::e_STARCAPTAIN: {
    return 3u;
  }
  case Rank::e_STARCOLONEL: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool
CoalitionBidHonorTraceCase::rank_le(const CoalitionBidHonorTraceCase::Rank r1,
                                    const CoalitionBidHonorTraceCase::Rank r2) {
  return rank_to_nat(r1) <= rank_to_nat(r2);
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::may_issue_batchall(
    const CoalitionBidHonorTraceCase::Commander &c) {
  return rank_le(Rank::e_STARCAPTAIN, c.cmd_rank);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::weight_class_value(
    const CoalitionBidHonorTraceCase::WeightClass w) {
  switch (w) {
  case WeightClass::e_LIGHT: {
    return 10u;
  }
  case WeightClass::e_HEAVY: {
    return 15u;
  }
  case WeightClass::e_ASSAULT: {
    return 18u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_class_bonus(
    const CoalitionBidHonorTraceCase::UnitClass c) {
  switch (c) {
  case UnitClass::e_OMNIMECH: {
    return 20u;
  }
  case UnitClass::e_BATTLEMECH: {
    return 10u;
  }
  case UnitClass::e_ELEMENTAL: {
    return 15u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_skill(
    const CoalitionBidHonorTraceCase::Unit &u) {
  return (u.unit_gunnery + u.unit_piloting);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::skill_bv_multiplier_num(const unsigned int &skill) {
  if (skill <= 4u) {
    return 6u;
  } else {
    if (skill <= 6u) {
      return 5u;
    } else {
      if (skill <= 8u) {
        return 4u;
      } else {
        return 3u;
      }
    }
  }
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_base_bv(
    const CoalitionBidHonorTraceCase::Unit &u) {
  return (u.unit_tonnage * weight_class_value(u.unit_weight));
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_tech_bv(
    const CoalitionBidHonorTraceCase::Unit &u) {
  unsigned int base = unit_base_bv(u);
  if (u.unit_is_clan) {
    return (base + (2u ? base / 2u : 0));
  } else {
    return base;
  }
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::unit_battle_value(
    const CoalitionBidHonorTraceCase::Unit &u) {
  unsigned int tech_bv = unit_tech_bv(u);
  return (4u ? (tech_bv * skill_bv_multiplier_num(unit_skill(u))) / 4u : 0);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::unit_effective_combat_rating(
    const CoalitionBidHonorTraceCase::Unit &u) {
  return (unit_battle_value(u) + unit_class_bonus(u.unit_class));
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ForceMetrics
CoalitionBidHonorTraceCase::unit_to_metrics(
    const CoalitionBidHonorTraceCase::Unit &u) {
  return ForceMetrics{1u,
                      u.unit_tonnage,
                      [=]() mutable -> unsigned int {
                        if (u.unit_is_elite) {
                          return 1u;
                        } else {
                          return 0u;
                        }
                      }(),
                      [=]() mutable -> unsigned int {
                        if (u.unit_is_clan) {
                          return 1u;
                        } else {
                          return 0u;
                        }
                      }(),
                      unit_battle_value(u),
                      unit_effective_combat_rating(u)};
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ForceMetrics
CoalitionBidHonorTraceCase::metrics_add(
    const CoalitionBidHonorTraceCase::ForceMetrics &m1,
    const CoalitionBidHonorTraceCase::ForceMetrics &m2) {
  return ForceMetrics{(m1.fm_count + m2.fm_count),
                      (m1.fm_tonnage + m2.fm_tonnage),
                      (m1.fm_elite_count + m2.fm_elite_count),
                      (m1.fm_clan_count + m2.fm_clan_count),
                      (m1.fm_total_bv + m2.fm_total_bv),
                      (m1.fm_total_ecr + m2.fm_total_ecr)};
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ForceMetrics
CoalitionBidHonorTraceCase::force_metrics(
    const List<CoalitionBidHonorTraceCase::Unit> &f) {
  return f.template fold_right<CoalitionBidHonorTraceCase::ForceMetrics>(
      [](const CoalitionBidHonorTraceCase::Unit &u,
         const CoalitionBidHonorTraceCase::ForceMetrics &acc) {
        return metrics_add(unit_to_metrics(u), acc);
      },
      empty_metrics);
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::metrics_total_lt(
    const CoalitionBidHonorTraceCase::ForceMetrics &m1,
    const CoalitionBidHonorTraceCase::ForceMetrics &m2) {
  return m1.fm_total_ecr < m2.fm_total_ecr;
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Force
CoalitionBidHonorTraceCase::coalition_force(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c) {
  return c.template flat_map<CoalitionBidHonorTraceCase::Unit>(
      [](const CoalitionBidHonorTraceCase::CoalitionMember &c0) {
        return c0.cm_force;
      });
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ForceMetrics
CoalitionBidHonorTraceCase::coalition_metrics(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c) {
  return force_metrics(coalition_force(c));
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::coalition_contains_clan(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c,
    const CoalitionBidHonorTraceCase::Clan clan) {
  return c.existsb(
      [=](const CoalitionBidHonorTraceCase::CoalitionMember &m) mutable {
        return clan_eqb(m.cm_clan, clan);
      });
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::coalition_tonnage(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c) {
  return coalition_metrics(c).fm_tonnage;
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Coalition
CoalitionBidHonorTraceCase::update_coalition_force(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c,
    const unsigned int &idx, List<CoalitionBidHonorTraceCase::Unit> new_force) {
  if (std::holds_alternative<
          typename List<CoalitionBidHonorTraceCase::CoalitionMember>::Nil>(
          c.v())) {
    return List<CoalitionBidHonorTraceCase::CoalitionMember>::nil();
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<CoalitionBidHonorTraceCase::CoalitionMember>::Cons>(
        c.v());
    if (idx <= 0) {
      return List<CoalitionBidHonorTraceCase::CoalitionMember>::cons(
          CoalitionMember{d_a0.cm_clan, d_a0.cm_commander, new_force}, *(d_a1));
    } else {
      unsigned int n = idx - 1;
      return List<CoalitionBidHonorTraceCase::CoalitionMember>::cons(
          d_a0, update_coalition_force(*(d_a1), n, std::move(new_force)));
    }
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ForceMetrics
CoalitionBidHonorTraceCase::bid_metrics(
    const CoalitionBidHonorTraceCase::ForceBid &b) {
  return force_metrics(b.bid_force);
}

__attribute__((pure)) std::optional<CoalitionBidHonorTraceCase::Commander>
CoalitionBidHonorTraceCase::coalition_lead_commander(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c) {
  if (std::holds_alternative<
          typename List<CoalitionBidHonorTraceCase::CoalitionMember>::Nil>(
          c.v())) {
    return std::optional<CoalitionBidHonorTraceCase::Commander>();
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<CoalitionBidHonorTraceCase::CoalitionMember>::Cons>(
        c.v());
    return std::make_optional<CoalitionBidHonorTraceCase::Commander>(
        d_a0.cm_commander);
  }
}

__attribute__((pure)) std::optional<CoalitionBidHonorTraceCase::ForceBid>
CoalitionBidHonorTraceCase::coalition_to_bid(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c,
    const CoalitionBidHonorTraceCase::Side side) {
  auto _cs = coalition_lead_commander(c);
  if (_cs.has_value()) {
    const CoalitionBidHonorTraceCase::Commander &cmd = *_cs;
    return std::make_optional<CoalitionBidHonorTraceCase::ForceBid>(
        ForceBid{coalition_force(c), side, cmd});
  } else {
    return std::optional<CoalitionBidHonorTraceCase::ForceBid>();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Coalition
CoalitionBidHonorTraceCase::apply_coalition_member_bid(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c,
    const CoalitionBidHonorTraceCase::CoalitionMemberBid &cbid) {
  return update_coalition_force(c, cbid.cmb_member_index, cbid.cmb_new_force);
}

__attribute__((pure)) bool
CoalitionBidHonorTraceCase::valid_coalition_member_bid_b(
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c,
    const CoalitionBidHonorTraceCase::CoalitionMemberBid &cbid) {
  return (cbid.cmb_member_index < c.length() &&
          metrics_total_lt(
              force_metrics(cbid.cmb_new_force),
              force_metrics(
                  ListDef::template nth<CoalitionBidHonorTraceCase::Force>(
                      cbid.cmb_member_index,
                      c.template map<CoalitionBidHonorTraceCase::Force>(
                          [](const CoalitionBidHonorTraceCase::CoalitionMember
                                 &c0) { return c0.cm_force; }),
                      List<CoalitionBidHonorTraceCase::Unit>::nil()))));
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::is_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  switch (rs) {
  case ReadyStatus::e_NEITHERREADY: {
    return false;
  }
  case ReadyStatus::e_ATTACKERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return true;
    }
    case Side::e_DEFENDER: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_DEFENDERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return false;
    }
    case Side::e_DEFENDER: {
      return true;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_BOTHREADY: {
    return true;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ReadyStatus
CoalitionBidHonorTraceCase::set_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  switch (rs) {
  case ReadyStatus::e_NEITHERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return ReadyStatus::e_ATTACKERREADY;
    }
    case Side::e_DEFENDER: {
      return ReadyStatus::e_DEFENDERREADY;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_ATTACKERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return rs;
    }
    case Side::e_DEFENDER: {
      return ReadyStatus::e_BOTHREADY;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_DEFENDERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return ReadyStatus::e_BOTHREADY;
    }
    case Side::e_DEFENDER: {
      return rs;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_BOTHREADY: {
    return rs;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ReadyStatus
CoalitionBidHonorTraceCase::clear_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  switch (rs) {
  case ReadyStatus::e_NEITHERREADY: {
    return rs;
  }
  case ReadyStatus::e_ATTACKERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return ReadyStatus::e_NEITHERREADY;
    }
    case Side::e_DEFENDER: {
      return rs;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_DEFENDERREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return rs;
    }
    case Side::e_DEFENDER: {
      return ReadyStatus::e_NEITHERREADY;
    }
    default:
      std::unreachable();
    }
  }
  case ReadyStatus::e_BOTHREADY: {
    switch (side) {
    case Side::e_ATTACKER: {
      return ReadyStatus::e_DEFENDERREADY;
    }
    case Side::e_DEFENDER: {
      return ReadyStatus::e_ATTACKERREADY;
    }
    default:
      std::unreachable();
    }
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Force
CoalitionBidHonorTraceCase::coalition_state_force(
    const std::optional<List<CoalitionBidHonorTraceCase::CoalitionMember>> &cs,
    List<CoalitionBidHonorTraceCase::Unit> fallback) {
  if (cs.has_value()) {
    const List<CoalitionBidHonorTraceCase::CoalitionMember> &c = *cs;
    return coalition_force(c);
  } else {
    return fallback;
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::ledger_lookup(
    const List<std::pair<unsigned int, Z>> &ledger,
    const unsigned int &warrior_id) {
  if (std::holds_alternative<typename List<std::pair<unsigned int, Z>>::Nil>(
          ledger.v())) {
    return Z::z0();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::pair<unsigned int, Z>>::Cons>(ledger.v());
    const unsigned int &id = d_a0.first;
    const Z &honor = d_a0.second;
    if (id == warrior_id) {
      return honor;
    } else {
      return ledger_lookup(*(d_a1), warrior_id);
    }
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::ledger_update_by_id(
    const List<std::pair<unsigned int, Z>> &ledger, unsigned int warrior_id,
    Z new_honor) {
  if (std::holds_alternative<typename List<std::pair<unsigned int, Z>>::Nil>(
          ledger.v())) {
    return List<std::pair<unsigned int, Z>>::cons(
        std::make_pair(warrior_id, std::move(new_honor)),
        List<std::pair<unsigned int, Z>>::nil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::pair<unsigned int, Z>>::Cons>(ledger.v());
    const unsigned int &id = d_a0.first;
    const Z &honor = d_a0.second;
    if (id == warrior_id) {
      return List<std::pair<unsigned int, Z>>::cons(
          std::make_pair(id, std::move(new_honor)), *(d_a1));
    } else {
      return List<std::pair<unsigned int, Z>>::cons(
          std::make_pair(id, honor),
          ledger_update_by_id(*(d_a1), warrior_id, std::move(new_honor)));
    }
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::update_honor(
    const List<std::pair<unsigned int, Z>> &ledger,
    const CoalitionBidHonorTraceCase::Commander &actor, const Z &delta) {
  Z current = ledger_lookup(ledger, actor.cmd_id);
  return ledger_update_by_id(ledger, actor.cmd_id,
                             BinInt::add(std::move(current), delta));
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::refusal_honor_delta(
    const CoalitionBidHonorTraceCase::RefusalReason &r) {
  if (std::holds_alternative<typename CoalitionBidHonorTraceCase::
                                 RefusalReason::RefusalInsufficientRank>(
          r.v())) {
    return Z::z0();
  } else {
    return Z::zneg(Positive::xh());
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::protocol_honor_delta(
    const CoalitionBidHonorTraceCase::ProtocolAction &action) {
  if (std::holds_alternative<
          typename CoalitionBidHonorTraceCase::ProtocolAction::ActChallenge>(
          action.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename CoalitionBidHonorTraceCase::
                                        ProtocolAction::ActRespond>(
                 action.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename CoalitionBidHonorTraceCase::
                                        ProtocolAction::ActRefuse>(
                 action.v())) {
    const auto &[d_reason] = std::get<
        typename CoalitionBidHonorTraceCase::ProtocolAction::ActRefuse>(
        action.v());
    return refusal_honor_delta(d_reason);
  } else if (std::holds_alternative<
                 typename CoalitionBidHonorTraceCase::ProtocolAction::ActClose>(
                 action.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename CoalitionBidHonorTraceCase::
                                        ProtocolAction::ActWithdraw>(
                 action.v())) {
    return Z::zneg(Positive::xo(Positive::xh()));
  } else if (std::holds_alternative<typename CoalitionBidHonorTraceCase::
                                        ProtocolAction::ActBreakBid>(
                 action.v())) {
    return Z::zneg(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))));
  } else {
    return Z::z0();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::apply_action_honor(
    const CoalitionBidHonorTraceCase::BatchallState &state,
    const CoalitionBidHonorTraceCase::ProtocolAction &action) {
  auto _cs = state.bs_phase.action_actor_in_phase(action);
  if (_cs.has_value()) {
    const CoalitionBidHonorTraceCase::Commander &actor = *_cs;
    return update_honor(state.bs_honor, actor, protocol_honor_delta(action));
  } else {
    return state.bs_honor;
  }
}
