#include <epoch_cell_glyph_trace.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

__attribute__((pure)) Positive Pos::mul(const Positive &x, Positive y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    return add(y, Positive::xo(mul(*(d_a0), y)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xo(mul(*(d_a0), y));
  } else {
    return y;
  }
}

__attribute__((pure)) Comparison Pos::compare_cont(const Comparison r,
                                                   const Positive &x,
                                                   const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(r, *(d_a0), *(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(Comparison::e_GT, *(d_a0), *(d_a00));
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(Comparison::e_LT, *(d_a0), *(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(r, *(d_a0), *(d_a00));
    } else {
      return Comparison::e_GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return r;
    } else {
      return Comparison::e_LT;
    }
  }
}

__attribute__((pure)) Comparison Pos::compare(const Positive &_x0,
                                              const Positive &_x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
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

__attribute__((pure)) unsigned int Pos::to_nat(const Positive &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
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

__attribute__((pure)) Z BinInt::opp(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zneg(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zpos(d_a0);
  }
}

__attribute__((pure)) Z BinInt::sub(const Z &m, const Z &n) {
  return BinInt::add(m, BinInt::opp(n));
}

__attribute__((pure)) Z BinInt::mul(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::mul(d_a0, d_a00));
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::mul(d_a0, d_a00));
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zneg(Pos::mul(d_a0, d_a00));
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zpos(Pos::mul(d_a0, d_a00));
    }
  }
}

__attribute__((pure)) Comparison BinInt::compare(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Comparison::e_EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      return Comparison::e_LT;
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::compare(d_a0, d_a00);
    } else {
      return Comparison::e_GT;
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y.v());
      return Datatypes::CompOpp(Pos::compare(d_a0, d_a00));
    } else {
      return Comparison::e_LT;
    }
  }
}

__attribute__((pure)) bool BinInt::leb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

__attribute__((pure)) bool BinInt::ltb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_LT: {
    return true;
  }
  default: {
    return false;
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

__attribute__((pure)) unsigned int BinInt::to_nat(const Z &z) {
  if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(z.v());
    return Pos::to_nat(d_a0);
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<Z, Z> BinInt::pos_div_eucl(const Positive &a,
                                                           const Z &b) {
  if (std::holds_alternative<typename Positive::XI>(a.v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(a.v());
    auto _cs = BinInt::pos_div_eucl(*(d_a0), b);
    const Z &q = _cs.first;
    const Z &r = _cs.second;
    Z r_ = BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r),
                       Z::zpos(Positive::xh()));
    if (BinInt::ltb(r_, b)) {
      return std::make_pair(
          BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q), r_);
    } else {
      return std::make_pair(
          BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q),
                      Z::zpos(Positive::xh())),
          BinInt::sub(r_, b));
    }
  } else if (std::holds_alternative<typename Positive::XO>(a.v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(a.v());
    auto _cs = BinInt::pos_div_eucl(*(d_a0), b);
    const Z &q = _cs.first;
    const Z &r = _cs.second;
    Z r_ = BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r);
    if (BinInt::ltb(r_, b)) {
      return std::make_pair(
          BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q), r_);
    } else {
      return std::make_pair(
          BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), q),
                      Z::zpos(Positive::xh())),
          BinInt::sub(r_, b));
    }
  } else {
    if (BinInt::leb(Z::zpos(Positive::xo(Positive::xh())), b)) {
      return std::make_pair(Z::z0(), Z::zpos(Positive::xh()));
    } else {
      return std::make_pair(Z::zpos(Positive::xh()), Z::z0());
    }
  }
}

__attribute__((pure)) std::pair<Z, Z> BinInt::div_eucl(Z a, const Z &b) {
  if (std::holds_alternative<typename Z::Z0>(a.v())) {
    return std::make_pair(Z::z0(), Z::z0());
  } else if (std::holds_alternative<typename Z::Zpos>(a.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(a.v());
    if (std::holds_alternative<typename Z::Z0>(b.v())) {
      return std::make_pair(Z::z0(), a);
    } else if (std::holds_alternative<typename Z::Zpos>(b.v())) {
      return BinInt::pos_div_eucl(d_a0, b);
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(b.v());
      auto _cs = BinInt::pos_div_eucl(d_a0, Z::zpos(d_a00));
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
    const auto &[d_a0] = std::get<typename Z::Zneg>(a.v());
    if (std::holds_alternative<typename Z::Z0>(b.v())) {
      return std::make_pair(Z::z0(), a);
    } else if (std::holds_alternative<typename Z::Zpos>(b.v())) {
      auto _cs = BinInt::pos_div_eucl(d_a0, b);
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
      const auto &[d_a00] = std::get<typename Z::Zneg>(b.v());
      auto _cs = BinInt::pos_div_eucl(d_a0, Z::zpos(d_a00));
      const Z &q = _cs.first;
      const Z &r = _cs.second;
      return std::make_pair(q, BinInt::opp(r));
    }
  }
}

__attribute__((pure)) Z BinInt::div(const Z &a, const Z &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const Z &q = _cs.first;
  const Z &_x = _cs.second;
  return q;
}

__attribute__((pure)) Z BinInt::modulo(const Z &a, const Z &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const Z &_x = _cs.first;
  const Z &r = _cs.second;
  return r;
}

__attribute__((pure)) Z BinInt::abs(const Z &z) {
  if (std::holds_alternative<typename Z::Z0>(z.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(z.v());
    return Z::zpos(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(z.v());
    return Z::zpos(d_a0);
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::phase_code(
    const EpochCellGlyphTraceCase::LunarPhase p) {
  switch (p) {
  case LunarPhase::e_NEWMOON: {
    return 0u;
  }
  case LunarPhase::e_FIRSTQUARTER: {
    return 1u;
  }
  case LunarPhase::e_FULLMOON: {
    return 2u;
  }
  case LunarPhase::e_LASTQUARTER: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::phase_from_angle(const Z &angle_deg) {
  Z wrapped = BinInt::modulo(
      angle_deg,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(wrapped,
                  Z::zpos(Positive::xi(Positive::xo(Positive::xi(
                      Positive::xi(Positive::xo(Positive::xh())))))))) {
    return LunarPhase::e_NEWMOON;
  } else {
    if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xi(Positive::xi(
                                 Positive::xo(Positive::xo(Positive::xo(
                                     Positive::xo(Positive::xh())))))))))) {
      return LunarPhase::e_FIRSTQUARTER;
    } else {
      if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                   Positive::xo(Positive::xo(Positive::xi(
                                       Positive::xi(Positive::xh())))))))))) {
        return LunarPhase::e_FULLMOON;
      } else {
        if (BinInt::ltb(wrapped,
                        Z::zpos(Positive::xi(Positive::xi(Positive::xo(
                            Positive::xi(Positive::xi(Positive::xi(Positive::xo(
                                Positive::xo(Positive::xh()))))))))))) {
          return LunarPhase::e_LASTQUARTER;
        } else {
          return LunarPhase::e_NEWMOON;
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::zodiac_code(
    const EpochCellGlyphTraceCase::ZodiacSign z) {
  switch (z) {
  case ZodiacSign::e_ARIES: {
    return 0u;
  }
  case ZodiacSign::e_TAURUS: {
    return 1u;
  }
  case ZodiacSign::e_GEMINI: {
    return 2u;
  }
  case ZodiacSign::e_CANCER: {
    return 3u;
  }
  case ZodiacSign::e_LEO: {
    return 4u;
  }
  case ZodiacSign::e_VIRGO: {
    return 5u;
  }
  case ZodiacSign::e_LIBRA: {
    return 6u;
  }
  case ZodiacSign::e_SCORPIO: {
    return 7u;
  }
  case ZodiacSign::e_SAGITTARIUS: {
    return 8u;
  }
  case ZodiacSign::e_CAPRICORN: {
    return 9u;
  }
  case ZodiacSign::e_AQUARIUS: {
    return 10u;
  }
  case ZodiacSign::e_PISCES: {
    return 11u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool
EpochCellGlyphTraceCase::eclipse_possible_at_dial(const Z &dial_pos) {
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

__attribute__((pure)) EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::step(
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

__attribute__((pure)) EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::step_reverse(
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

__attribute__((pure)) EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::step_n(const unsigned int &n,
                                EpochCellGlyphTraceCase::MechanismState s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int rest = n - 1;
    return step_n(rest, step(s));
  }
}

__attribute__((pure)) EpochCellGlyphTraceCase::MechanismState
EpochCellGlyphTraceCase::state_at_cell(Z cell) {
  return MechanismState{cell, cell, cell, cell, cell, cell, cell};
}

__attribute__((pure)) EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::predict_moon_phase_from_state(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  Z phase_angle = BinInt::div(
      BinInt::mul(s.metonic_dial,
                  Z::zpos(Positive::xo(Positive::xo(
                      Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                          Positive::xi(Positive::xo(Positive::xh())))))))))),
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))))));
  return phase_from_angle(phase_angle);
}

__attribute__((pure)) Z EpochCellGlyphTraceCase::predict_olympiad_year(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  return BinInt::add(
      BinInt::modulo(s.games_dial,
                     Z::zpos(Positive::xo(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xh()));
}

__attribute__((pure)) EpochCellGlyphTraceCase::ZodiacSign
EpochCellGlyphTraceCase::predict_zodiac_sign(
    const EpochCellGlyphTraceCase::MechanismState &s) {
  Z deg = BinInt::modulo(
      s.zodiac_position,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(
                           Positive::xi(Positive::xi(Positive::xh()))))))) {
    return ZodiacSign::e_ARIES;
  } else {
    if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                             Positive::xi(Positive::xi(Positive::xh())))))))) {
      return ZodiacSign::e_TAURUS;
    } else {
      if (BinInt::ltb(
              deg, Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                       Positive::xi(Positive::xo(Positive::xh()))))))))) {
        return ZodiacSign::e_GEMINI;
      } else {
        if (BinInt::ltb(
                deg,
                Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(
                    Positive::xi(Positive::xi(Positive::xh()))))))))) {
          return ZodiacSign::e_CANCER;
        } else {
          if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(Positive::xi(
                                   Positive::xo(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xh())))))))))) {
            return ZodiacSign::e_LEO;
          } else {
            if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                                     Positive::xo(Positive::xi(Positive::xi(
                                         Positive::xo(Positive::xh())))))))))) {
              return ZodiacSign::e_VIRGO;
            } else {
              if (BinInt::ltb(deg,
                              Z::zpos(Positive::xo(Positive::xi(Positive::xo(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xi(Positive::xh())))))))))) {
                return ZodiacSign::e_LIBRA;
              } else {
                if (BinInt::ltb(deg,
                                Z::zpos(Positive::xo(Positive::xo(Positive::xo(
                                    Positive::xo(Positive::xi(Positive::xi(
                                        Positive::xi(Positive::xh())))))))))) {
                  return ZodiacSign::e_SCORPIO;
                } else {
                  if (BinInt::ltb(
                          deg, Z::zpos(Positive::xo(Positive::xi(
                                   Positive::xi(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xo(Positive::xo(
                                           Positive::xh()))))))))))) {
                    return ZodiacSign::e_SAGITTARIUS;
                  } else {
                    if (BinInt::ltb(
                            deg, Z::zpos(Positive::xo(Positive::xo(
                                     Positive::xi(Positive::xi(Positive::xo(
                                         Positive::xi(Positive::xo(Positive::xo(
                                             Positive::xh()))))))))))) {
                      return ZodiacSign::e_CAPRICORN;
                    } else {
                      if (BinInt::ltb(
                              deg,
                              Z::zpos(Positive::xo(Positive::xi(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xo(Positive::xi(Positive::xo(
                                          Positive::xh()))))))))))) {
                        return ZodiacSign::e_AQUARIUS;
                      } else {
                        return ZodiacSign::e_PISCES;
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

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::eclipse_category_code(
    const EpochCellGlyphTraceCase::EclipseCategory c) {
  switch (c) {
  case EclipseCategory::e_EC_TOTALLUNAR: {
    return 0u;
  }
  case EclipseCategory::e_EC_PARTIALLUNAR: {
    return 1u;
  }
  case EclipseCategory::e_EC_TOTALSOLAR: {
    return 2u;
  }
  case EclipseCategory::e_EC_ANNULARSOLAR: {
    return 3u;
  }
  case EclipseCategory::e_EC_PARTIALSOLAR: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::glyph_code(
    const EpochCellGlyphTraceCase::DialGlyph g) {
  switch (g) {
  case DialGlyph::e_GLYPH_SIGMA: {
    return 0u;
  }
  case DialGlyph::e_GLYPH_ETA: {
    return 1u;
  }
  case DialGlyph::e_GLYPH_SIGMATOTAL: {
    return 2u;
  }
  case DialGlyph::e_GLYPH_ETAANNULAR: {
    return 3u;
  }
  case DialGlyph::e_GLYPH_EMPTY: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::category_matches_glyph(
    const EpochCellGlyphTraceCase::EclipseCategory cat,
    const EpochCellGlyphTraceCase::DialGlyph g) {
  switch (cat) {
  case EclipseCategory::e_EC_TOTALLUNAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return true;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case EclipseCategory::e_EC_PARTIALLUNAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  case EclipseCategory::e_EC_ANNULARSOLAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_ETA: {
      return true;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  default: {
    switch (g) {
    case DialGlyph::e_GLYPH_ETA: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
  }
}

__attribute__((pure)) EpochCellGlyphTraceCase::DialGlyph
EpochCellGlyphTraceCase::glyph_at_cell(const Z &cell) {
  if (BinInt::eqb(cell, Z::z0())) {
    return DialGlyph::e_GLYPH_SIGMATOTAL;
  } else {
    if (BinInt::eqb(cell,
                    Z::zpos(Positive::xo(Positive::xi(Positive::xh()))))) {
      return DialGlyph::e_GLYPH_SIGMA;
    } else {
      if (BinInt::eqb(cell, Z::zpos(Positive::xo(
                                Positive::xo(Positive::xi(Positive::xh())))))) {
        return DialGlyph::e_GLYPH_ETA;
      } else {
        if (BinInt::eqb(cell, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                  Positive::xo(Positive::xh()))))))) {
          return DialGlyph::e_GLYPH_SIGMA;
        } else {
          return DialGlyph::e_GLYPH_EMPTY;
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::count_total_lunar(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    List<EpochCellGlyphTraceCase::HistoricalEclipse> d_a1_value =
        clone_as_value<List<HistoricalEclipse>>(d_a1);
    unsigned int count_here = [&]() {
      switch (d_a0.he_category) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        return 1u;
      }
      default: {
        return 0u;
      }
      }
    }();
    return (count_here + count_total_lunar(d_a1_value));
  }
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::count_visible_total_lunar(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    List<EpochCellGlyphTraceCase::HistoricalEclipse> d_a1_value =
        clone_as_value<List<HistoricalEclipse>>(d_a1);
    unsigned int count_here = [&]() {
      switch (d_a0.he_category) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        if (d_a0.he_visible_mediterranean) {
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
    return (count_here + count_visible_total_lunar(d_a1_value));
  }
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::visible_series_checksum(
    const List<EpochCellGlyphTraceCase::HistoricalEclipse> &es) {
  if (std::holds_alternative<
          typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Nil>(
          es.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<EpochCellGlyphTraceCase::HistoricalEclipse>::Cons>(
        es.v());
    unsigned int term;
    if (d_a0.he_visible_mediterranean) {
      term = BinInt::to_nat(BinInt::abs(d_a0.he_saros_series));
    } else {
      term = 0u;
    }
    return (term + visible_series_checksum(*(d_a1)));
  }
}

__attribute__((pure)) Z EpochCellGlyphTraceCase::months_from_epoch(
    const Z &epoch_year, const Z &eclipse_year, const Z &epoch_month,
    const Z &eclipse_month) {
  Z year_diff = BinInt::sub(epoch_year, eclipse_year);
  Z month_diff = BinInt::sub(eclipse_month, epoch_month);
  return BinInt::add(
      BinInt::mul(year_diff, Z::zpos(Positive::xo(
                                 Positive::xo(Positive::xi(Positive::xh()))))),
      month_diff);
}

__attribute__((pure)) Z EpochCellGlyphTraceCase::saros_cell(
    const Z &epoch_year, const Z &epoch_month,
    const EpochCellGlyphTraceCase::HistoricalEclipse &e) {
  Z months = months_from_epoch(epoch_year, e.he_year, epoch_month, e.he_month);
  return BinInt::modulo(
      months,
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

__attribute__((pure)) Z EpochCellGlyphTraceCase::saros_dial_at_month(
    const Z &start_cell, const Z &months) {
  return BinInt::modulo(
      BinInt::add(start_cell, months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

__attribute__((pure)) EpochCellGlyphTraceCase::EpochReading
EpochCellGlyphTraceCase::build_epoch_reading(
    const Z &epoch_year, const Z &epoch_month,
    EpochCellGlyphTraceCase::HistoricalEclipse e) {
  Z cell = saros_cell(epoch_year, epoch_month, e);
  return EpochReading{state_at_cell(cell), e, cell, glyph_at_cell(cell)};
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::reading_matches(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return category_matches_glyph(reading.reading_eclipse.he_category,
                                reading.reading_glyph);
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_phase_code(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return phase_code(predict_moon_phase_from_state(reading.reading_state));
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_zodiac_code(
    const EpochCellGlyphTraceCase::EpochReading &reading) {
  return zodiac_code(predict_zodiac_sign(reading.reading_state));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::phase_code_after_steps(const unsigned int &n) {
  return phase_code(predict_moon_phase_from_state(step_n(n, initial_state)));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::zodiac_code_after_steps(const unsigned int &n) {
  return zodiac_code(predict_zodiac_sign(step_n(n, initial_state)));
}

__attribute__((pure)) Comparison Datatypes::CompOpp(const Comparison r) {
  switch (r) {
  case Comparison::e_EQ: {
    return Comparison::e_EQ;
  }
  case Comparison::e_LT: {
    return Comparison::e_GT;
  }
  case Comparison::e_GT: {
    return Comparison::e_LT;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool QArith_base::Qle_bool(const Q &x, const Q &y) {
  return BinInt::leb(BinInt::mul(x.Qnum, Z::zpos(y.Qden)),
                     BinInt::mul(y.Qnum, Z::zpos(x.Qden)));
}
