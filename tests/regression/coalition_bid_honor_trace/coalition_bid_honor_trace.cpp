#include <coalition_bid_honor_trace.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::eqb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::leb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::ltb(const unsigned int n,
                                         const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
PeanoNat::divmod(const unsigned int x, const unsigned int y,
                 const unsigned int q, const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return PeanoNat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return PeanoNat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::div(const unsigned int x,
                                                 const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return PeanoNat::divmod(x, y_, 0u, y_).first;
  }
}

std::shared_ptr<Positive> Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::xo(succ(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xi(_args.d_a0);
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xo(Positive::xh());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(_args.d_a0);
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(Overloaded{[](const typename Positive::XI _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(
                                               succ(_args0.d_a0));
                                         },
                                         [](const typename Positive::XO _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xi(_args0.d_a0);
                                         },
                                         [](const typename Positive::XH _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(Positive::xh());
                                         }},
                              y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add_carry(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XO _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xo(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XH _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(succ(_args.d_a0));
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(Positive::xh());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::xi(Positive::xo(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xi(pred_double(_args.d_a0));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xh();
          }},
      x->v());
}

__attribute__((pure)) bool Pos::eqb(const std::shared_ptr<Positive> &p,
                                    const std::shared_ptr<Positive> &q) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> bool {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0) -> bool {
                             return eqb(_args.d_a0, _args0.d_a0);
                           },
                           [](const typename Positive::XO _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return false;
                           }},
                q->v());
          },
          [&](const typename Positive::XO _args) -> bool {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0) -> bool {
                             return false;
                           },
                           [&](const typename Positive::XO _args0) -> bool {
                             return eqb(_args.d_a0, _args0.d_a0);
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return false;
                           }},
                q->v());
          },
          [&](const typename Positive::XH _args) -> bool {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XO _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return true;
                           }},
                q->v());
          }},
      p->v());
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xo(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xo(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xh());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xi(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Pos::pred_double(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xh());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Pos::pred_double(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xi(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::double_(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::succ_double(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zpos(Positive::xo(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::pred_double(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::double_(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zpos(Pos::pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zneg(Positive::xo(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zneg(Pos::pred_double(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> { return Z::z0(); }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Z> BinInt::add(std::shared_ptr<Z> x, std::shared_ptr<Z> y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
            return std::move(y);
          },
          [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
                _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args0)
                            -> std::shared_ptr<Z> {
                          return Z::zpos(Pos::add(_args.d_a0, _args0.d_a0));
                        },
                        [&](const typename Z::Zneg _args0)
                            -> std::shared_ptr<Z> {
                          return BinInt::pos_sub(_args.d_a0, _args0.d_a0);
                        }},
                    std::move(y)->v());
              }
            }();
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 2) {
                auto &_rf = std::get<2>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
                _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args0)
                            -> std::shared_ptr<Z> {
                          return BinInt::pos_sub(_args0.d_a0, _args.d_a0);
                        },
                        [&](const typename Z::Zneg _args0)
                            -> std::shared_ptr<Z> {
                          return Z::zneg(Pos::add(_args.d_a0, _args0.d_a0));
                        }},
                    std::move(y)->v());
              }
            }();
          }},
      x->v());
}

__attribute__((pure)) bool BinInt::eqb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return true; },
                    [](const typename Z::Zpos _args0) -> bool { return false; },
                    [](const typename Z::Zneg _args0) -> bool {
                      return false;
                    }},
                y->v());
          },
          [&](const typename Z::Zpos _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return false; },
                    [&](const typename Z::Zpos _args0) -> bool {
                      return Pos::eqb(_args.d_a0, _args0.d_a0);
                    },
                    [](const typename Z::Zneg _args0) -> bool {
                      return false;
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return false; },
                    [](const typename Z::Zpos _args0) -> bool { return false; },
                    [&](const typename Z::Zneg _args0) -> bool {
                      return Pos::eqb(_args.d_a0, _args0.d_a0);
                    }},
                y->v());
          }},
      x->v());
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::clan_eq_dec(
    const CoalitionBidHonorTraceCase::Clan c1,
    const CoalitionBidHonorTraceCase::Clan c2) {
  return [&](void) {
    switch (c1) {
    case Clan::e_CLANWOLF: {
      return [&](void) {
        switch (c2) {
        case Clan::e_CLANWOLF: {
          return true;
        }
        case Clan::e_CLANJADEFALCON: {
          return false;
        }
        case Clan::e_CLANGHOSTBEAR: {
          return false;
        }
        }
      }();
    }
    case Clan::e_CLANJADEFALCON: {
      return [&](void) {
        switch (c2) {
        case Clan::e_CLANWOLF: {
          return false;
        }
        case Clan::e_CLANJADEFALCON: {
          return true;
        }
        case Clan::e_CLANGHOSTBEAR: {
          return false;
        }
        }
      }();
    }
    case Clan::e_CLANGHOSTBEAR: {
      return [&](void) {
        switch (c2) {
        case Clan::e_CLANWOLF: {
          return false;
        }
        case Clan::e_CLANJADEFALCON: {
          return false;
        }
        case Clan::e_CLANGHOSTBEAR: {
          return true;
        }
        }
      }();
    }
    }
  }();
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
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) bool
CoalitionBidHonorTraceCase::rank_le(const CoalitionBidHonorTraceCase::Rank r1,
                                    const CoalitionBidHonorTraceCase::Rank r2) {
  return PeanoNat::leb(rank_to_nat(r1), rank_to_nat(r2));
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::may_issue_batchall(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Commander> &c) {
  return rank_le(Rank::e_STARCAPTAIN, c->cmd_rank);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::weight_class_value(
    const CoalitionBidHonorTraceCase::WeightClass w) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_class_bonus(
    const CoalitionBidHonorTraceCase::UnitClass c) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_skill(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Unit> &u) {
  return (u->unit_gunnery + u->unit_piloting);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::skill_bv_multiplier_num(const unsigned int skill) {
  if (PeanoNat::leb(skill, 4u)) {
    return 6u;
  } else {
    if (PeanoNat::leb(skill, 6u)) {
      return 5u;
    } else {
      if (PeanoNat::leb(skill, 8u)) {
        return 4u;
      } else {
        return 3u;
      }
    }
  }
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_base_bv(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Unit> &u) {
  return (u->unit_tonnage * weight_class_value(u->unit_weight));
}

__attribute__((pure)) unsigned int CoalitionBidHonorTraceCase::unit_tech_bv(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Unit> &u) {
  unsigned int base = unit_base_bv(u);
  if (u->unit_is_clan) {
    return (base + PeanoNat::div(base, 2u));
  } else {
    return std::move(base);
  }
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::unit_battle_value(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Unit> &u) {
  unsigned int tech_bv = unit_tech_bv(u);
  return PeanoNat::div(
      (std::move(tech_bv) * skill_bv_multiplier_num(unit_skill(u))), 4u);
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::unit_effective_combat_rating(
    const std::shared_ptr<CoalitionBidHonorTraceCase::Unit> &u) {
  return (unit_battle_value(u) + unit_class_bonus(u->unit_class));
}

std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>
CoalitionBidHonorTraceCase::unit_to_metrics(
    std::shared_ptr<CoalitionBidHonorTraceCase::Unit> u) {
  return std::make_shared<CoalitionBidHonorTraceCase::ForceMetrics>(
      ForceMetrics{1u, u->unit_tonnage,
                   [&](void) {
                     if (u->unit_is_elite) {
                       return 1u;
                     } else {
                       return 0u;
                     }
                   }(),
                   [&](void) {
                     if (u->unit_is_clan) {
                       return 1u;
                     } else {
                       return 0u;
                     }
                   }(),
                   unit_battle_value(u), unit_effective_combat_rating(u)});
}

std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>
CoalitionBidHonorTraceCase::metrics_add(
    std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics> m1,
    std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics> m2) {
  return std::make_shared<CoalitionBidHonorTraceCase::ForceMetrics>(
      ForceMetrics{(m1->fm_count + m2->fm_count),
                   (m1->fm_tonnage + m2->fm_tonnage),
                   (m1->fm_elite_count + m2->fm_elite_count),
                   (m1->fm_clan_count + m2->fm_clan_count),
                   (m1->fm_total_bv + m2->fm_total_bv),
                   (m1->fm_total_ecr + m2->fm_total_ecr)});
}

std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>
CoalitionBidHonorTraceCase::force_metrics(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::Unit>>> &f) {
  return f->template fold_right<
      std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>>(
      [](std::shared_ptr<CoalitionBidHonorTraceCase::Unit> u,
         std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics> acc) {
        return metrics_add(unit_to_metrics(u), acc);
      },
      empty_metrics);
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::metrics_total_lt(
    const std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics> &m1,
    const std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics> &m2) {
  return PeanoNat::ltb(m1->fm_total_ecr, m2->fm_total_ecr);
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Force
CoalitionBidHonorTraceCase::coalition_force(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        &c) {
  return c
      ->template flat_map<std::shared_ptr<CoalitionBidHonorTraceCase::Unit>>(
          [](std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember> c0) {
            return c0->cm_force;
          });
}

std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>
CoalitionBidHonorTraceCase::coalition_metrics(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        &c) {
  return force_metrics(coalition_force(c));
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::coalition_contains_clan(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>> &c,
    const CoalitionBidHonorTraceCase::Clan clan) {
  return c->existsb(
      [=](std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>
              m) mutable { return clan_eqb(m->cm_clan, clan); });
}

__attribute__((pure)) unsigned int
CoalitionBidHonorTraceCase::coalition_tonnage(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        &c) {
  return coalition_metrics(c)->fm_tonnage;
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Coalition
CoalitionBidHonorTraceCase::update_coalition_force(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>> &c,
    const unsigned int idx,
    std::shared_ptr<List<std::shared_ptr<CoalitionBidHonorTraceCase::Unit>>>
        new_force) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<
                 CoalitionBidHonorTraceCase::CoalitionMember>>::Nil _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  CoalitionBidHonorTraceCase::CoalitionMember>>> {
            return List<std::shared_ptr<
                CoalitionBidHonorTraceCase::CoalitionMember>>::nil();
          },
          [&](const typename List<std::shared_ptr<
                  CoalitionBidHonorTraceCase::CoalitionMember>>::Cons _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  CoalitionBidHonorTraceCase::CoalitionMember>>> {
            if (idx <= 0) {
              return List<std::shared_ptr<
                  CoalitionBidHonorTraceCase::CoalitionMember>>::
                  cons(std::make_shared<
                           CoalitionBidHonorTraceCase::CoalitionMember>(
                           CoalitionMember{_args.d_a0->cm_clan,
                                           _args.d_a0->cm_commander,
                                           std::move(new_force)}),
                       _args.d_a1);
            } else {
              unsigned int n = idx - 1;
              return List<std::shared_ptr<
                  CoalitionBidHonorTraceCase::CoalitionMember>>::
                  cons(std::move(_args.d_a0),
                       update_coalition_force(_args.d_a1, n, new_force));
            }
          }},
      c->v());
}

std::shared_ptr<CoalitionBidHonorTraceCase::ForceMetrics>
CoalitionBidHonorTraceCase::bid_metrics(
    const std::shared_ptr<CoalitionBidHonorTraceCase::ForceBid> &b) {
  return force_metrics(b->bid_force);
}

__attribute__((pure))
std::optional<std::shared_ptr<CoalitionBidHonorTraceCase::Commander>>
CoalitionBidHonorTraceCase::coalition_lead_commander(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        &c) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<
                 CoalitionBidHonorTraceCase::CoalitionMember>>::Nil _args)
              -> std::optional<
                  std::shared_ptr<CoalitionBidHonorTraceCase::Commander>> {
            return std::optional<
                std::shared_ptr<CoalitionBidHonorTraceCase::Commander>>();
          },
          [](const typename List<std::shared_ptr<
                 CoalitionBidHonorTraceCase::CoalitionMember>>::Cons _args)
              -> std::optional<
                  std::shared_ptr<CoalitionBidHonorTraceCase::Commander>> {
            return std::make_optional<
                std::shared_ptr<CoalitionBidHonorTraceCase::Commander>>(
                _args.d_a0->cm_commander);
          }},
      c->v());
}

__attribute__((pure))
std::optional<std::shared_ptr<CoalitionBidHonorTraceCase::ForceBid>>
CoalitionBidHonorTraceCase::coalition_to_bid(
    std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        c,
    const CoalitionBidHonorTraceCase::Side side) {
  if (coalition_lead_commander(c).has_value()) {
    std::shared_ptr<CoalitionBidHonorTraceCase::Commander> cmd =
        *coalition_lead_commander(c);
    return std::make_optional<
        std::shared_ptr<CoalitionBidHonorTraceCase::ForceBid>>(
        std::make_shared<CoalitionBidHonorTraceCase::ForceBid>(
            ForceBid{coalition_force(c), std::move(side), cmd}));
  } else {
    return std::optional<
        std::shared_ptr<CoalitionBidHonorTraceCase::ForceBid>>();
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Coalition
CoalitionBidHonorTraceCase::apply_coalition_member_bid(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>> &c,
    const std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMemberBid>
        &cbid) {
  return update_coalition_force(c, cbid->cmb_member_index, cbid->cmb_new_force);
}

__attribute__((pure)) bool
CoalitionBidHonorTraceCase::valid_coalition_member_bid_b(
    const std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>> &c,
    const std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMemberBid>
        &cbid) {
  return (PeanoNat::ltb(cbid->cmb_member_index, c->length()) &&
          metrics_total_lt(
              force_metrics(cbid->cmb_new_force),
              force_metrics(
                  c->template map<CoalitionBidHonorTraceCase::Force>(
                       [](std::shared_ptr<
                           CoalitionBidHonorTraceCase::CoalitionMember>
                              c0) { return c0->cm_force; })
                      ->nth(cbid->cmb_member_index,
                            List<std::shared_ptr<
                                CoalitionBidHonorTraceCase::Unit>>::nil()))));
}

__attribute__((pure)) bool CoalitionBidHonorTraceCase::is_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  return [&](void) {
    switch (rs) {
    case ReadyStatus::e_NEITHERREADY: {
      return false;
    }
    case ReadyStatus::e_ATTACKERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return true;
        }
        case Side::e_DEFENDER: {
          return false;
        }
        }
      }();
    }
    case ReadyStatus::e_DEFENDERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return false;
        }
        case Side::e_DEFENDER: {
          return true;
        }
        }
      }();
    }
    case ReadyStatus::e_BOTHREADY: {
      return true;
    }
    }
  }();
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ReadyStatus
CoalitionBidHonorTraceCase::set_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  return [&](void) {
    switch (rs) {
    case ReadyStatus::e_NEITHERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return ReadyStatus::e_ATTACKERREADY;
        }
        case Side::e_DEFENDER: {
          return ReadyStatus::e_DEFENDERREADY;
        }
        }
      }();
    }
    case ReadyStatus::e_ATTACKERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return rs;
        }
        case Side::e_DEFENDER: {
          return ReadyStatus::e_BOTHREADY;
        }
        }
      }();
    }
    case ReadyStatus::e_DEFENDERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return ReadyStatus::e_BOTHREADY;
        }
        case Side::e_DEFENDER: {
          return rs;
        }
        }
      }();
    }
    case ReadyStatus::e_BOTHREADY: {
      return rs;
    }
    }
  }();
}

__attribute__((pure)) CoalitionBidHonorTraceCase::ReadyStatus
CoalitionBidHonorTraceCase::clear_ready(
    const CoalitionBidHonorTraceCase::ReadyStatus rs,
    const CoalitionBidHonorTraceCase::Side side) {
  return [&](void) {
    switch (rs) {
    case ReadyStatus::e_NEITHERREADY: {
      return rs;
    }
    case ReadyStatus::e_ATTACKERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return ReadyStatus::e_NEITHERREADY;
        }
        case Side::e_DEFENDER: {
          return rs;
        }
        }
      }();
    }
    case ReadyStatus::e_DEFENDERREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return rs;
        }
        case Side::e_DEFENDER: {
          return ReadyStatus::e_NEITHERREADY;
        }
        }
      }();
    }
    case ReadyStatus::e_BOTHREADY: {
      return [&](void) {
        switch (side) {
        case Side::e_ATTACKER: {
          return ReadyStatus::e_DEFENDERREADY;
        }
        case Side::e_DEFENDER: {
          return ReadyStatus::e_ATTACKERREADY;
        }
        }
      }();
    }
    }
  }();
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Force
CoalitionBidHonorTraceCase::coalition_state_force(
    const std::optional<std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>>
        cs,
    std::shared_ptr<List<std::shared_ptr<CoalitionBidHonorTraceCase::Unit>>>
        fallback) {
  if (cs.has_value()) {
    std::shared_ptr<
        List<std::shared_ptr<CoalitionBidHonorTraceCase::CoalitionMember>>>
        c = *cs;
    return coalition_force(std::move(c));
  } else {
    return std::move(fallback);
  }
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::ledger_lookup(
    const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
        &ledger,
    const unsigned int warrior_id) {
  return std::visit(
      Overloaded{[](const typename List<
                     std::pair<unsigned int, std::shared_ptr<Z>>>::Nil _args)
                     -> std::shared_ptr<Z> { return Z::z0(); },
                 [&](const typename List<
                     std::pair<unsigned int, std::shared_ptr<Z>>>::Cons _args)
                     -> std::shared_ptr<Z> {
                   unsigned int id = _args.d_a0.first;
                   std::shared_ptr<Z> honor = _args.d_a0.second;
                   if (PeanoNat::eqb(id, warrior_id)) {
                     return honor;
                   } else {
                     return ledger_lookup(_args.d_a1, warrior_id);
                   }
                 }},
      ledger->v());
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::ledger_update_by_id(
    const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
        &ledger,
    const unsigned int warrior_id, std::shared_ptr<Z> new_honor) {
  return std::visit(
      Overloaded{
          [&](const typename List<
              std::pair<unsigned int, std::shared_ptr<Z>>>::Nil _args)
              -> std::shared_ptr<
                  List<std::pair<unsigned int, std::shared_ptr<Z>>>> {
            return List<std::pair<unsigned int, std::shared_ptr<Z>>>::cons(
                std::make_pair(std::move(warrior_id), std::move(new_honor)),
                List<std::pair<unsigned int, std::shared_ptr<Z>>>::nil());
          },
          [&](const typename List<
              std::pair<unsigned int, std::shared_ptr<Z>>>::Cons _args)
              -> std::shared_ptr<
                  List<std::pair<unsigned int, std::shared_ptr<Z>>>> {
            unsigned int id = _args.d_a0.first;
            std::shared_ptr<Z> honor = _args.d_a0.second;
            if (PeanoNat::eqb(id, warrior_id)) {
              return List<std::pair<unsigned int, std::shared_ptr<Z>>>::cons(
                  std::make_pair(id, new_honor), std::move(_args.d_a1));
            } else {
              return List<std::pair<unsigned int, std::shared_ptr<Z>>>::cons(
                  std::make_pair(id, honor),
                  ledger_update_by_id(std::move(_args.d_a1), warrior_id,
                                      new_honor));
            }
          }},
      ledger->v());
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::update_honor(
    const std::shared_ptr<List<std::pair<unsigned int, std::shared_ptr<Z>>>>
        &ledger,
    const std::shared_ptr<CoalitionBidHonorTraceCase::Commander> &actor,
    const std::shared_ptr<Z> &delta) {
  std::shared_ptr<Z> current = ledger_lookup(ledger, actor->cmd_id);
  return ledger_update_by_id(ledger, actor->cmd_id,
                             BinInt::add(std::move(current), delta));
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::refusal_honor_delta(
    const std::shared_ptr<CoalitionBidHonorTraceCase::RefusalReason> &r) {
  return std::visit(
      Overloaded{[](const typename CoalitionBidHonorTraceCase::RefusalReason::
                        RefusalInsufficientRank _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename CoalitionBidHonorTraceCase::RefusalReason::
                        RefusalOther _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xh());
                 }},
      r->v());
}

__attribute__((pure)) CoalitionBidHonorTraceCase::Honor
CoalitionBidHonorTraceCase::protocol_honor_delta(
    const std::shared_ptr<CoalitionBidHonorTraceCase::ProtocolAction> &action) {
  return std::visit(
      Overloaded{
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActChallenge _args) -> std::shared_ptr<Z> {
            return Z::zpos(Positive::xh());
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActRespond _args) -> std::shared_ptr<Z> {
            return Z::zpos(Positive::xh());
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActRefuse _args) -> std::shared_ptr<Z> {
            return refusal_honor_delta(_args.d_a0);
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::ActBid
                 _args) -> std::shared_ptr<Z> { return Z::z0(); },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActCoalitionBid _args) -> std::shared_ptr<Z> {
            return Z::z0();
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::ActPass
                 _args) -> std::shared_ptr<Z> { return Z::z0(); },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::ActClose
                 _args) -> std::shared_ptr<Z> {
            return Z::zpos(Positive::xh());
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActWithdraw _args) -> std::shared_ptr<Z> {
            return Z::zneg(Positive::xo(Positive::xh()));
          },
          [](const typename CoalitionBidHonorTraceCase::ProtocolAction::
                 ActBreakBid _args) -> std::shared_ptr<Z> {
            return Z::zneg(
                Positive::xo(Positive::xi(Positive::xo(Positive::xh()))));
          }},
      action->v());
}

__attribute__((pure)) CoalitionBidHonorTraceCase::HonorLedger
CoalitionBidHonorTraceCase::apply_action_honor(
    const std::shared_ptr<CoalitionBidHonorTraceCase::BatchallState> &state,
    const std::shared_ptr<CoalitionBidHonorTraceCase::ProtocolAction> &action) {
  if (state->bs_phase->action_actor_in_phase(action).has_value()) {
    std::shared_ptr<CoalitionBidHonorTraceCase::Commander> actor =
        *state->bs_phase->action_actor_in_phase(action);
    return update_honor(state->bs_honor, actor, protocol_honor_delta(action));
  } else {
    return state->bs_honor;
  }
}
