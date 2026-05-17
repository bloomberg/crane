#include "epoch_cell_glyph_trace.h"

Positive Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(*a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

Positive Pos::add(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add(*a0, *a00));
    } else {
      return Positive::xi(*a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(succ(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(*a00);
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

Positive Pos::add_carry(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else {
      return Positive::xi(succ(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(succ(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(succ(*a00));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

Positive Pos::pred_double(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xi(Positive::xo(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(pred_double(*a0));
  } else {
    return Positive::xh();
  }
}

Positive Pos::mul(const Positive &x, Positive y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return add(y, Positive::xo(mul(*a0, y)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xo(mul(*a0, std::move(y)));
  } else {
    return y;
  }
}

Comparison Pos::compare_cont(Comparison r, const Positive &x,
                             const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(r, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(Comparison::GT, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(Comparison::LT, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(r, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return r;
    } else {
      return Comparison::LT;
    }
  }
}

Comparison Pos::compare(const Positive &_x0, const Positive &_x1) {
  return compare_cont(Comparison::EQ, _x0, _x1);
}

bool Pos::eqb(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return eqb(*a0, *a00);
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return eqb(*a0, *a00);
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

unsigned int Pos::to_nat(const Positive &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

Z BinInt::double_(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xo(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xo(a0));
  }
}

Z BinInt::succ_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xi(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Pos::pred_double(a0));
  }
}

Z BinInt::pred_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zneg(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Pos::pred_double(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xi(a0));
  }
}

Z BinInt::pos_sub(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return BinInt::double_(BinInt::pos_sub(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return BinInt::succ_double(BinInt::pos_sub(*a0, *a00));
    } else {
      return Z::zpos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return BinInt::pred_double(BinInt::pos_sub(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return BinInt::double_(BinInt::pos_sub(*a0, *a00));
    } else {
      return Z::zpos(Pos::pred_double(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Z::zneg(Positive::xo(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Z::zneg(Pos::pred_double(*a00));
    } else {
      return Z::z0();
    }
  }
}

Z BinInt::add(Z x, Z y) {
  if (std::holds_alternative<typename Z::Z0>(x.v_mut())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x.v_mut())) {
    auto &[a0] = std::get<typename Z::Zpos>(x.v_mut());
    if (std::holds_alternative<typename Z::Z0>(y.v_mut())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v_mut())) {
      auto &[a00] = std::get<typename Z::Zpos>(y.v_mut());
      return Z::zpos(Pos::add(std::move(a0), std::move(a00)));
    } else {
      auto &[a00] = std::get<typename Z::Zneg>(y.v_mut());
      return BinInt::pos_sub(std::move(a0), std::move(a00));
    }
  } else {
    auto &[a0] = std::get<typename Z::Zneg>(x.v_mut());
    if (std::holds_alternative<typename Z::Z0>(y.v_mut())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v_mut())) {
      auto &[a00] = std::get<typename Z::Zpos>(y.v_mut());
      return BinInt::pos_sub(std::move(a00), std::move(a0));
    } else {
      auto &[a00] = std::get<typename Z::Zneg>(y.v_mut());
      return Z::zneg(Pos::add(std::move(a0), std::move(a00)));
    }
  }
}

Z BinInt::opp(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zneg(a0);
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zpos(a0);
  }
}

Z BinInt::sub(const Z &m, const Z &n) { return BinInt::add(m, BinInt::opp(n)); }

Z BinInt::mul(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::mul(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::mul(a0, a00));
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zneg(Pos::mul(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zpos(Pos::mul(a0, a00));
    }
  }
}

Comparison BinInt::compare(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Comparison::EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      return Comparison::LT;
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::compare(a0, a00);
    } else {
      return Comparison::GT;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Datatypes::CompOpp(Pos::compare(a0, a00));
    } else {
      return Comparison::LT;
    }
  }
}

bool BinInt::leb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

bool BinInt::ltb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool BinInt::eqb(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  }
}

unsigned int BinInt::to_nat(const Z &z) {
  if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Pos::to_nat(a0);
  } else {
    return 0u;
  }
}

std::pair<Z, Z> BinInt::pos_div_eucl(const Positive &a, const Z &b) {
  if (std::holds_alternative<typename Positive::XI>(a.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(a.v());
    auto _cs = BinInt::pos_div_eucl(*a0, b);
    const Z &q = _cs.first;
    const Z &r = _cs.second;
    Z r_ = BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r),
                       Z::zpos(Positive::xh()));
    if (BinInt::ltb(r_, b)) {
      return std::make_pair(
          BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q), std::move(r_));
    } else {
      return std::make_pair(
          BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q),
                      Z::zpos(Positive::xh())),
          BinInt::sub(std::move(r_), b));
    }
  } else if (std::holds_alternative<typename Positive::XO>(a.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(a.v());
    auto _cs = BinInt::pos_div_eucl(*a0, b);
    const Z &q = _cs.first;
    const Z &r = _cs.second;
    Z r_ = BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r);
    if (BinInt::ltb(r_, b)) {
      return std::make_pair(
          BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q), std::move(r_));
    } else {
      return std::make_pair(
          BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q),
                      Z::zpos(Positive::xh())),
          BinInt::sub(std::move(r_), b));
    }
  } else {
    if (BinInt::leb(Z::zpos(Positive::xo(Positive::xh())), b)) {
      return std::make_pair(Z::z0(), Z::zpos(Positive::xh()));
    } else {
      return std::make_pair(Z::zpos(Positive::xh()), Z::z0());
    }
  }
}

std::pair<Z, Z> BinInt::div_eucl(Z a, const Z &b) {
  if (std::holds_alternative<typename Z::Z0>(a.v_mut())) {
    return std::make_pair(Z::z0(), Z::z0());
  } else if (std::holds_alternative<typename Z::Zpos>(a.v_mut())) {
    auto &[a0] = std::get<typename Z::Zpos>(a.v_mut());
    if (std::holds_alternative<typename Z::Z0>(b.v())) {
      return std::make_pair(Z::z0(), a);
    } else if (std::holds_alternative<typename Z::Zpos>(b.v())) {
      return BinInt::pos_div_eucl(std::move(a0), b);
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(b.v());
      auto _cs = BinInt::pos_div_eucl(a0, Z::zpos(a00));
      const Z &q = _cs.first;
      const Z &r = _cs.second;
      if (std::holds_alternative<typename Z::Z0>(r.v())) {
        return std::make_pair(BinInt::opp(q), Z::z0());
      } else {
        return std::make_pair(
            BinInt::opp(BinInt::add(q, Z::zpos(Positive::xh()))),
            BinInt::add(b, r));
      }
    }
  } else {
    auto &[a0] = std::get<typename Z::Zneg>(a.v_mut());
    if (std::holds_alternative<typename Z::Z0>(b.v())) {
      return std::make_pair(Z::z0(), a);
    } else if (std::holds_alternative<typename Z::Zpos>(b.v())) {
      auto _cs = BinInt::pos_div_eucl(a0, b);
      const Z &q = _cs.first;
      const Z &r = _cs.second;
      if (std::holds_alternative<typename Z::Z0>(r.v())) {
        return std::make_pair(BinInt::opp(q), Z::z0());
      } else {
        return std::make_pair(
            BinInt::opp(BinInt::add(q, Z::zpos(Positive::xh()))),
            BinInt::sub(b, r));
      }
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(b.v());
      auto _cs = BinInt::pos_div_eucl(a0, Z::zpos(a00));
      const Z &q = _cs.first;
      const Z &r = _cs.second;
      return std::make_pair(std::move(_cs.first), BinInt::opp(r));
    }
  }
}

Z BinInt::div(const Z &a, const Z &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const Z &q = _cs.first;
  const Z &_x = _cs.second;
  return q;
}

Z BinInt::modulo(const Z &a, const Z &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const Z &_x = _cs.first;
  const Z &r = _cs.second;
  return r;
}

Z BinInt::abs(const Z &z) {
  if (std::holds_alternative<typename Z::Z0>(z.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Z::zpos(a0);
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(z.v());
    return Z::zpos(a0);
  }
}

unsigned int
EpochCellGlyphTraceCase::phase_code(EpochCellGlyphTraceCase::LunarPhase p) {
  switch (p) {
  case LunarPhase::NEWMOON: {
    return 0u;
  }
  case LunarPhase::FIRSTQUARTER: {
    return 1u;
  }
  case LunarPhase::FULLMOON: {
    return 2u;
  }
  case LunarPhase::LASTQUARTER: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::phase_from_angle(const Z &angle_deg) {
  Z wrapped = BinInt::modulo(
      angle_deg,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(wrapped,
                  Z::zpos(Positive::xi(Positive::xo(Positive::xi(
                      Positive::xi(Positive::xo(Positive::xh())))))))) {
    return LunarPhase::NEWMOON;
  } else {
    if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xi(Positive::xi(
                                 Positive::xo(Positive::xo(Positive::xo(
                                     Positive::xo(Positive::xh())))))))))) {
      return LunarPhase::FIRSTQUARTER;
    } else {
      if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                   Positive::xo(Positive::xo(Positive::xi(
                                       Positive::xi(Positive::xh())))))))))) {
        return LunarPhase::FULLMOON;
      } else {
        if (BinInt::ltb(std::move(wrapped),
                        Z::zpos(Positive::xi(Positive::xi(Positive::xo(
                            Positive::xi(Positive::xi(Positive::xi(Positive::xo(
                                Positive::xo(Positive::xh()))))))))))) {
          return LunarPhase::LASTQUARTER;
        } else {
          return LunarPhase::NEWMOON;
        }
      }
    }
  }
}

unsigned int
EpochCellGlyphTraceCase::zodiac_code(EpochCellGlyphTraceCase::ZodiacSign z) {
  switch (z) {
  case ZodiacSign::ARIES: {
    return 0u;
  }
  case ZodiacSign::TAURUS: {
    return 1u;
  }
  case ZodiacSign::GEMINI: {
    return 2u;
  }
  case ZodiacSign::CANCER: {
    return 3u;
  }
  case ZodiacSign::LEO: {
    return 4u;
  }
  case ZodiacSign::VIRGO: {
    return 5u;
  }
  case ZodiacSign::LIBRA: {
    return 6u;
  }
  case ZodiacSign::SCORPIO: {
    return 7u;
  }
  case ZodiacSign::SAGITTARIUS: {
    return 8u;
  }
  case ZodiacSign::CAPRICORN: {
    return 9u;
  }
  case ZodiacSign::AQUARIUS: {
    return 10u;
  }
  case ZodiacSign::PISCES: {
    return 11u;
  }
  default:
    std::unreachable();
  }
}

bool EpochCellGlyphTraceCase::eclipse_possible_at_dial(const Z &dial_pos) {
  if (BinInt::eqb(dial_pos, Z::zpos(Positive::xh()))) {
    return true;
  } else {
    if (BinInt::eqb(dial_pos,
                    Z::zpos(Positive::xo(Positive::xi(Positive::xh()))))) {
      return true;
    } else {
      if (BinInt::eqb(dial_pos, Z::zpos(Positive::xo(Positive::xo(
                                    Positive::xi(Positive::xh())))))) {
        return true;
      } else {
        if (BinInt::eqb(dial_pos,
                        Z::zpos(Positive::xi(Positive::xo(
                            Positive::xo(Positive::xo(Positive::xh()))))))) {
          return true;
        } else {
          return false;
        }
      }
    }
  }
}

EpochCellGlyphTraceCase::MechanismState EpochCellGlyphTraceCase::step(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  return MechanismState{
      BinInt::add(s.crank_position, Z::zpos(Positive::xh())),
      BinInt::modulo(BinInt::add(s.metonic_dial, Z::zpos(Positive::xh())),
                     metonic_modulus),
      BinInt::modulo(BinInt::add(s.saros_dial, Z::zpos(Positive::xh())),
                     saros_modulus),
      BinInt::modulo(BinInt::add(s.callippic_dial, Z::zpos(Positive::xh())),
                     callippic_modulus),
      BinInt::modulo(BinInt::add(s.exeligmos_dial, Z::zpos(Positive::xh())),
                     exeligmos_modulus),
      BinInt::modulo(BinInt::add(s.games_dial, Z::zpos(Positive::xh())),
                     games_modulus),
      BinInt::modulo(BinInt::add(s.zodiac_position, Z::zpos(Positive::xh())),
                     zodiac_modulus)};
}

EpochCellGlyphTraceCase::MechanismState EpochCellGlyphTraceCase::step_reverse(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  return MechanismState{
      BinInt::sub(s.crank_position, Z::zpos(Positive::xh())),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.metonic_dial, Z::zpos(Positive::xh())),
                      metonic_modulus),
          metonic_modulus),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.saros_dial, Z::zpos(Positive::xh())),
                      saros_modulus),
          saros_modulus),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.callippic_dial, Z::zpos(Positive::xh())),
                      callippic_modulus),
          callippic_modulus),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.exeligmos_dial, Z::zpos(Positive::xh())),
                      exeligmos_modulus),
          exeligmos_modulus),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.games_dial, Z::zpos(Positive::xh())),
                      games_modulus),
          games_modulus),
      BinInt::modulo(
          BinInt::add(BinInt::sub(s.zodiac_position, Z::zpos(Positive::xh())),
                      zodiac_modulus),
          zodiac_modulus)};
}

EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::step_n(unsigned int n,
                                EpochCellGlyphTraceCase::MechanismState s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int rest = n - 1;
    return step_n(rest, step(std::move(s)));
  }
}

EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::state_at_cell(Z cell) {
  return MechanismState{cell, cell, cell, cell, cell, cell, cell};
}

EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::predict_moon_phase_from_state(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  Z phase_angle = BinInt::div(
      BinInt::mul(s.metonic_dial,
                  Z::zpos(Positive::xo(Positive::xo(
                      Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                          Positive::xi(Positive::xo(Positive::xh())))))))))),
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))))));
  return phase_from_angle(std::move(phase_angle));
}

Z EpochCellGlyphTraceCase::predict_olympiad_year(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  return BinInt::add(
      BinInt::modulo(s.games_dial,
                     Z::zpos(Positive::xo(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xh()));
}

EpochCellGlyphTraceCase::ZodiacSign
EpochCellGlyphTraceCase::predict_zodiac_sign(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  Z deg = BinInt::modulo(
      s.zodiac_position,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(
                           Positive::xi(Positive::xi(Positive::xh()))))))) {
    return ZodiacSign::ARIES;
  } else {
    if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                             Positive::xi(Positive::xi(Positive::xh())))))))) {
      return ZodiacSign::TAURUS;
    } else {
      if (BinInt::ltb(
              deg, Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                       Positive::xi(Positive::xo(Positive::xh()))))))))) {
        return ZodiacSign::GEMINI;
      } else {
        if (BinInt::ltb(
                deg,
                Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(
                    Positive::xi(Positive::xi(Positive::xh()))))))))) {
          return ZodiacSign::CANCER;
        } else {
          if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(Positive::xi(
                                   Positive::xo(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xh())))))))))) {
            return ZodiacSign::LEO;
          } else {
            if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                                     Positive::xo(Positive::xi(Positive::xi(
                                         Positive::xo(Positive::xh())))))))))) {
              return ZodiacSign::VIRGO;
            } else {
              if (BinInt::ltb(deg,
                              Z::zpos(Positive::xo(Positive::xi(Positive::xo(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xi(Positive::xh())))))))))) {
                return ZodiacSign::LIBRA;
              } else {
                if (BinInt::ltb(deg,
                                Z::zpos(Positive::xo(Positive::xo(Positive::xo(
                                    Positive::xo(Positive::xi(Positive::xi(
                                        Positive::xi(Positive::xh())))))))))) {
                  return ZodiacSign::SCORPIO;
                } else {
                  if (BinInt::ltb(
                          deg, Z::zpos(Positive::xo(Positive::xi(
                                   Positive::xi(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xo(Positive::xo(
                                           Positive::xh()))))))))))) {
                    return ZodiacSign::SAGITTARIUS;
                  } else {
                    if (BinInt::ltb(
                            deg, Z::zpos(Positive::xo(Positive::xo(
                                     Positive::xi(Positive::xi(Positive::xo(
                                         Positive::xi(Positive::xo(Positive::xo(
                                             Positive::xh()))))))))))) {
                      return ZodiacSign::CAPRICORN;
                    } else {
                      if (BinInt::ltb(
                              std::move(deg),
                              Z::zpos(Positive::xo(Positive::xi(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xo(Positive::xi(Positive::xo(
                                          Positive::xh()))))))))))) {
                        return ZodiacSign::AQUARIUS;
                      } else {
                        return ZodiacSign::PISCES;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

unsigned int EpochCellGlyphTraceCase::eclipse_category_code(
    EpochCellGlyphTraceCase::EclipseCategory c) {
  switch (c) {
  case EclipseCategory::EC_TOTALLUNAR: {
    return 0u;
  }
  case EclipseCategory::EC_PARTIALLUNAR: {
    return 1u;
  }
  case EclipseCategory::EC_TOTALSOLAR: {
    return 2u;
  }
  case EclipseCategory::EC_ANNULARSOLAR: {
    return 3u;
  }
  case EclipseCategory::EC_PARTIALSOLAR: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

unsigned int
EpochCellGlyphTraceCase::glyph_code(EpochCellGlyphTraceCase::DialGlyph g) {
  switch (g) {
  case DialGlyph::GLYPH_SIGMA: {
    return 0u;
  }
  case DialGlyph::GLYPH_ETA: {
    return 1u;
  }
  case DialGlyph::GLYPH_SIGMATOTAL: {
    return 2u;
  }
  case DialGlyph::GLYPH_ETAANNULAR: {
    return 3u;
  }
  case DialGlyph::GLYPH_EMPTY: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

bool EpochCellGlyphTraceCase::category_matches_glyph(
    EpochCellGlyphTraceCase::EclipseCategory cat,
    EpochCellGlyphTraceCase::DialGlyph g) {
  switch (cat) {
  case EclipseCategory::EC_TOTALLUNAR: {
    switch (g) {
    case DialGlyph::GLYPH_SIGMA: {
      return true;
    }
    case DialGlyph::GLYPH_SIGMATOTAL: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case EclipseCategory::EC_PARTIALLUNAR: {
    switch (g) {
    case DialGlyph::GLYPH_SIGMA: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case EclipseCategory::EC_ANNULARSOLAR: {
    switch (g) {
    case DialGlyph::GLYPH_ETA: {
      return true;
    }
    case DialGlyph::GLYPH_ETAANNULAR: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  default: {
    switch (g) {
    case DialGlyph::GLYPH_ETA: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  }
}

EpochCellGlyphTraceCase::DialGlyph
EpochCellGlyphTraceCase::glyph_at_cell(const Z &cell) {
  if (BinInt::eqb(cell, Z::z0())) {
    return DialGlyph::GLYPH_SIGMATOTAL;
  } else {
    if (BinInt::eqb(cell,
                    Z::zpos(Positive::xo(Positive::xi(Positive::xh()))))) {
      return DialGlyph::GLYPH_SIGMA;
    } else {
      if (BinInt::eqb(cell, Z::zpos(Positive::xo(
                                Positive::xo(Positive::xi(Positive::xh())))))) {
        return DialGlyph::GLYPH_ETA;
      } else {
        if (BinInt::eqb(cell, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                  Positive::xo(Positive::xh()))))))) {
          return DialGlyph::GLYPH_SIGMA;
        } else {
          return DialGlyph::GLYPH_EMPTY;
        }
      }
    }
  }
}

unsigned int EpochCellGlyphTraceCase::count_total_lunar(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    unsigned int count_here = [&]() {
      switch (a0.he_category) {
      case EclipseCategory::EC_TOTALLUNAR: {
        return 1u;
      }
      default: {
        return 0u;
      }
      }
    }();
    return (count_here + count_total_lunar(*a1));
  }
}

unsigned int EpochCellGlyphTraceCase::count_visible_total_lunar(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    unsigned int count_here = [&]() {
      switch (a0.he_category) {
      case EclipseCategory::EC_TOTALLUNAR: {
        if (a0.he_visible_mediterranean) {
          return 1u;
        } else {
          return 0u;
        }
      }
      default: {
        return 0u;
      }
      }
    }();
    return (count_here + count_visible_total_lunar(*a1));
  }
}

unsigned int EpochCellGlyphTraceCase::visible_series_checksum(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    unsigned int term;
    if (a0.he_visible_mediterranean) {
      term = BinInt::to_nat(BinInt::abs(a0.he_saros_series));
    } else {
      term = 0u;
    }
    return (term + visible_series_checksum(*a1));
  }
}

Z EpochCellGlyphTraceCase::months_from_epoch(const Z &epoch_year,
                                             const Z &eclipse_year,
                                             const Z &epoch_month,
                                             const Z &eclipse_month) {
  Z year_diff = BinInt::sub(epoch_year, eclipse_year);
  Z month_diff = BinInt::sub(eclipse_month, epoch_month);
  return BinInt::add(
      BinInt::mul(std::move(year_diff), Z::zpos(Positive::xo(Positive::xo(
                                            Positive::xi(Positive::xh()))))),
      std::move(month_diff));
}

Z EpochCellGlyphTraceCase::saros_cell(
    const Z &epoch_year, const Z &epoch_month,
    const EpochCellGlyphTraceCase::HistoricalEclipse &e) {
  Z months = months_from_epoch(epoch_year, e.he_year, epoch_month, e.he_month);
  return BinInt::modulo(
      std::move(months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

Z EpochCellGlyphTraceCase::saros_dial_at_month(const Z &start_cell,
                                               const Z &months) {
  return BinInt::modulo(
      BinInt::add(start_cell, months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

EpochCellGlyphTraceCase::EpochReading
EpochCellGlyphTraceCase::build_epoch_reading(
    const Z &epoch_year, const Z &epoch_month,
    EpochCellGlyphTraceCase::HistoricalEclipse e) {
  Z cell = saros_cell(epoch_year, epoch_month, e);
  return EpochReading{state_at_cell(cell), e, cell, glyph_at_cell(cell)};
}

bool EpochCellGlyphTraceCase::reading_matches(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return category_matches_glyph(reading.reading_eclipse.he_category,
                                reading.reading_glyph);
}

unsigned int EpochCellGlyphTraceCase::reading_phase_code(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return phase_code(predict_moon_phase_from_state(reading.reading_state));
}

unsigned int EpochCellGlyphTraceCase::reading_zodiac_code(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return zodiac_code(predict_zodiac_sign(reading.reading_state));
}

unsigned int EpochCellGlyphTraceCase::phase_code_after_steps(unsigned int n) {
  return phase_code(predict_moon_phase_from_state(step_n(n, initial_state)));
}

unsigned int EpochCellGlyphTraceCase::zodiac_code_after_steps(unsigned int n) {
  return zodiac_code(predict_zodiac_sign(step_n(n, initial_state)));
}

Comparison Datatypes::CompOpp(Comparison r) {
  switch (r) {
  case Comparison::EQ: {
    return Comparison::EQ;
  }
  case Comparison::LT: {
    return Comparison::GT;
  }
  case Comparison::GT: {
    return Comparison::LT;
  }
  default:
    std::unreachable();
  }
}

bool QArith_base::Qle_bool(const Q &x, const Q &y) {
  return BinInt::leb(BinInt::mul(x.Qnum, Z::zpos(y.Qden)),
                     BinInt::mul(y.Qnum, Z::zpos(x.Qden)));
}
