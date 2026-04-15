#include <epoch_cell_glyph_trace.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Positive> Pos::succ(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    return Positive::xo(succ(_m.d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    return Positive::xi(_m.d_a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

std::shared_ptr<Positive> Pos::add(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xo(add_carry(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xi(add(_m.d_a0, _m0.d_a0));
    } else {
      return Positive::xo(succ(_m.d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xi(add(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xo(add(_m.d_a0, _m0.d_a0));
    } else {
      return Positive::xi(_m.d_a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xo(succ(_m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xi(_m0.d_a0);
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

std::shared_ptr<Positive> Pos::add_carry(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xi(add_carry(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xo(add_carry(_m.d_a0, _m0.d_a0));
    } else {
      return Positive::xi(succ(_m.d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xo(add_carry(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xi(add(_m.d_a0, _m0.d_a0));
    } else {
      return Positive::xo(succ(_m.d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Positive::xi(succ(_m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Positive::xo(succ(_m0.d_a0));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    return Positive::xi(Positive::xo(_m.d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    return Positive::xi(pred_double(_m.d_a0));
  } else {
    return Positive::xh();
  }
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    return add(y, Positive::xo(mul(_m.d_a0, y)));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    return Positive::xo(mul(_m.d_a0, y));
  } else {
    return y;
  }
}

__attribute__((pure)) Comparison
Pos::compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
                  const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return compare_cont(r, _m.d_a0, _m0.d_a0);
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return compare_cont(Comparison::e_GT, _m.d_a0, _m0.d_a0);
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return compare_cont(Comparison::e_LT, _m.d_a0, _m0.d_a0);
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return compare_cont(r, _m.d_a0, _m0.d_a0);
    } else {
      return Comparison::e_GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y->v())) {
      return r;
    } else {
      return Comparison::e_LT;
    }
  }
}

__attribute__((pure)) Comparison
Pos::compare(const std::shared_ptr<Positive> &_x0,
             const std::shared_ptr<Positive> &_x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
}

__attribute__((pure)) bool Pos::eqb(const std::shared_ptr<Positive> &p,
                                    const std::shared_ptr<Positive> &q) {
  if (std::holds_alternative<typename Positive::XI>(p->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&p->v());
    if (std::holds_alternative<typename Positive::XI>(q->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&q->v());
      return eqb(_m.d_a0, _m0.d_a0);
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&p->v());
    if (std::holds_alternative<typename Positive::XO>(q->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&q->v());
      return eqb(_m.d_a0, _m0.d_a0);
    } else {
      return false;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(q->v())) {
      return true;
    } else {
      return false;
    }
  }
}

__attribute__((pure)) unsigned int
Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    return Z::zpos(Positive::xo(_m.d_a0));
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    return Z::zneg(Positive::xo(_m.d_a0));
  }
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    return Z::zpos(Positive::xi(_m.d_a0));
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    return Z::zneg(Pos::pred_double(_m.d_a0));
  }
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::zneg(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    return Z::zpos(Pos::pred_double(_m.d_a0));
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    return Z::zneg(Positive::xi(_m.d_a0));
  }
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return BinInt::double_(BinInt::pos_sub(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return BinInt::succ_double(BinInt::pos_sub(_m.d_a0, _m0.d_a0));
    } else {
      return Z::zpos(Positive::xo(_m.d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return BinInt::pred_double(BinInt::pos_sub(_m.d_a0, _m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return BinInt::double_(BinInt::pos_sub(_m.d_a0, _m0.d_a0));
    } else {
      return Z::zpos(Pos::pred_double(_m.d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XI>(&y->v());
      return Z::zneg(Positive::xo(_m0.d_a0));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &_m0 = *std::get_if<typename Positive::XO>(&y->v());
      return Z::zneg(Pos::pred_double(_m0.d_a0));
    } else {
      return Z::z0();
    }
  }
}

std::shared_ptr<Z> BinInt::add(std::shared_ptr<Z> x, std::shared_ptr<Z> y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    if (std::holds_alternative<typename Z::Zpos>(y->v()) &&
        y.use_count() == 1) {
      auto &_rf = std::get<1>(y->v_mut());
      std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
      _rf.d_a0 = Pos::add(std::move(_m.d_a0), y_);
      return y;
    } else if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return Z::zpos(Pos::add(_m.d_a0, _m0.d_a0));
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return BinInt::pos_sub(_m.d_a0, _m0.d_a0);
    }
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    if (std::holds_alternative<typename Z::Zneg>(y->v()) &&
        y.use_count() == 1) {
      auto &_rf = std::get<2>(y->v_mut());
      std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
      _rf.d_a0 = Pos::add(std::move(_m.d_a0), y_);
      return y;
    } else if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return BinInt::pos_sub(_m0.d_a0, _m.d_a0);
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return Z::zneg(Pos::add(_m.d_a0, _m0.d_a0));
    }
  }
}

std::shared_ptr<Z> BinInt::opp(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    return Z::zneg(_m.d_a0);
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    return Z::zpos(_m.d_a0);
  }
}

std::shared_ptr<Z> BinInt::sub(const std::shared_ptr<Z> &m,
                               const std::shared_ptr<Z> &n) {
  return BinInt::add(m, BinInt::opp(n));
}

std::shared_ptr<Z> BinInt::mul(const std::shared_ptr<Z> &x,
                               const std::shared_ptr<Z> &y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return Z::zpos(Pos::mul(_m.d_a0, _m0.d_a0));
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return Z::zneg(Pos::mul(_m.d_a0, _m0.d_a0));
    }
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return Z::zneg(Pos::mul(_m.d_a0, _m0.d_a0));
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return Z::zpos(Pos::mul(_m.d_a0, _m0.d_a0));
    }
  }
}

__attribute__((pure)) Comparison BinInt::compare(const std::shared_ptr<Z> &x,
                                                 const std::shared_ptr<Z> &y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Comparison::e_EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      return Comparison::e_LT;
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return Pos::compare(_m.d_a0, _m0.d_a0);
    } else {
      return Comparison::e_GT;
    }
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    if (std::holds_alternative<typename Z::Zneg>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return Datatypes::CompOpp(Pos::compare(_m.d_a0, _m0.d_a0));
    } else {
      return Comparison::e_LT;
    }
  }
}

__attribute__((pure)) bool BinInt::leb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

__attribute__((pure)) bool BinInt::ltb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

__attribute__((pure)) bool BinInt::eqb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&x->v());
    if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zpos>(&y->v());
      return Pos::eqb(_m.d_a0, _m0.d_a0);
    } else {
      return false;
    }
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&x->v());
    if (std::holds_alternative<typename Z::Zneg>(y->v())) {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&y->v());
      return Pos::eqb(_m.d_a0, _m0.d_a0);
    } else {
      return false;
    }
  }
}

__attribute__((pure)) unsigned int BinInt::to_nat(const std::shared_ptr<Z> &z) {
  if (std::holds_alternative<typename Z::Zpos>(z->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&z->v());
    return Pos::to_nat(_m.d_a0);
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
BinInt::pos_div_eucl(const std::shared_ptr<Positive> &a,
                     const std::shared_ptr<Z> &b) {
  if (std::holds_alternative<typename Positive::XI>(a->v())) {
    const auto &_m = *std::get_if<typename Positive::XI>(&a->v());
    auto _cs = BinInt::pos_div_eucl(_m.d_a0, b);
    const std::shared_ptr<Z> &q = _cs.first;
    const std::shared_ptr<Z> &r = _cs.second;
    std::shared_ptr<Z> r_ =
        BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r),
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
  } else if (std::holds_alternative<typename Positive::XO>(a->v())) {
    const auto &_m = *std::get_if<typename Positive::XO>(&a->v());
    auto _cs = BinInt::pos_div_eucl(_m.d_a0, b);
    const std::shared_ptr<Z> &q = _cs.first;
    const std::shared_ptr<Z> &r = _cs.second;
    std::shared_ptr<Z> r_ =
        BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r);
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

__attribute__((pure)) std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
BinInt::div_eucl(std::shared_ptr<Z> a, const std::shared_ptr<Z> &b) {
  if (std::holds_alternative<typename Z::Z0>(a->v())) {
    return std::make_pair(Z::z0(), Z::z0());
  } else if (std::holds_alternative<typename Z::Zpos>(a->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&a->v());
    if (std::holds_alternative<typename Z::Z0>(b->v())) {
      return std::make_pair(Z::z0(), std::move(a));
    } else if (std::holds_alternative<typename Z::Zpos>(b->v())) {
      return BinInt::pos_div_eucl(_m.d_a0, b);
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&b->v());
      auto _cs = BinInt::pos_div_eucl(_m.d_a0, Z::zpos(_m0.d_a0));
      const std::shared_ptr<Z> &q = _cs.first;
      const std::shared_ptr<Z> &r = _cs.second;
      if (std::holds_alternative<typename Z::Z0>(r->v())) {
        return std::make_pair(BinInt::opp(q), Z::z0());
      } else {
        return std::make_pair(
            BinInt::opp(BinInt::add(q, Z::zpos(Positive::xh()))),
            BinInt::add(b, r));
      }
    }
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&a->v());
    if (std::holds_alternative<typename Z::Z0>(b->v())) {
      return std::make_pair(Z::z0(), std::move(a));
    } else if (std::holds_alternative<typename Z::Zpos>(b->v())) {
      auto _cs = BinInt::pos_div_eucl(_m.d_a0, b);
      const std::shared_ptr<Z> &q = _cs.first;
      const std::shared_ptr<Z> &r = _cs.second;
      if (std::holds_alternative<typename Z::Z0>(r->v())) {
        return std::make_pair(BinInt::opp(q), Z::z0());
      } else {
        return std::make_pair(
            BinInt::opp(BinInt::add(q, Z::zpos(Positive::xh()))),
            BinInt::sub(b, r));
      }
    } else {
      const auto &_m0 = *std::get_if<typename Z::Zneg>(&b->v());
      auto _cs = BinInt::pos_div_eucl(_m.d_a0, Z::zpos(_m0.d_a0));
      const std::shared_ptr<Z> &q = _cs.first;
      const std::shared_ptr<Z> &r = _cs.second;
      return std::make_pair(q, BinInt::opp(r));
    }
  }
}

std::shared_ptr<Z> BinInt::div(const std::shared_ptr<Z> &a,
                               const std::shared_ptr<Z> &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const std::shared_ptr<Z> &q = _cs.first;
  const std::shared_ptr<Z> &_x = _cs.second;
  return q;
}

std::shared_ptr<Z> BinInt::modulo(const std::shared_ptr<Z> &a,
                                  const std::shared_ptr<Z> &b) {
  auto _cs = BinInt::div_eucl(a, b);
  const std::shared_ptr<Z> &_x = _cs.first;
  const std::shared_ptr<Z> &r = _cs.second;
  return r;
}

std::shared_ptr<Z> BinInt::abs(const std::shared_ptr<Z> &z) {
  if (std::holds_alternative<typename Z::Z0>(z->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z->v())) {
    const auto &_m = *std::get_if<typename Z::Zpos>(&z->v());
    return Z::zpos(_m.d_a0);
  } else {
    const auto &_m = *std::get_if<typename Z::Zneg>(&z->v());
    return Z::zpos(_m.d_a0);
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
EpochCellGlyphTraceCase::phase_from_angle(const std::shared_ptr<Z> &angle_deg) {
  std::shared_ptr<Z> wrapped = BinInt::modulo(
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
        if (BinInt::ltb(std::move(wrapped),
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

__attribute__((pure)) bool EpochCellGlyphTraceCase::eclipse_possible_at_dial(
    const std::shared_ptr<Z> &dial_pos) {
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

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  return std::make_shared<
      EpochCellGlyphTraceCase::MechanismState>(MechanismState{
      BinInt::add(s->crank_position, Z::zpos(Positive::xh())),
      BinInt::modulo(BinInt::add(s->metonic_dial, Z::zpos(Positive::xh())),
                     metonic_modulus),
      BinInt::modulo(BinInt::add(s->saros_dial, Z::zpos(Positive::xh())),
                     saros_modulus),
      BinInt::modulo(BinInt::add(s->callippic_dial, Z::zpos(Positive::xh())),
                     callippic_modulus),
      BinInt::modulo(BinInt::add(s->exeligmos_dial, Z::zpos(Positive::xh())),
                     exeligmos_modulus),
      BinInt::modulo(BinInt::add(s->games_dial, Z::zpos(Positive::xh())),
                     games_modulus),
      BinInt::modulo(BinInt::add(s->zodiac_position, Z::zpos(Positive::xh())),
                     zodiac_modulus)});
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step_reverse(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  return std::make_shared<EpochCellGlyphTraceCase::MechanismState>(
      MechanismState{
          BinInt::sub(s->crank_position, Z::zpos(Positive::xh())),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->metonic_dial, Z::zpos(Positive::xh())),
                          metonic_modulus),
              metonic_modulus),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->saros_dial, Z::zpos(Positive::xh())),
                          saros_modulus),
              saros_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->callippic_dial,
                                                 Z::zpos(Positive::xh())),
                                     callippic_modulus),
                         callippic_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->exeligmos_dial,
                                                 Z::zpos(Positive::xh())),
                                     exeligmos_modulus),
                         exeligmos_modulus),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->games_dial, Z::zpos(Positive::xh())),
                          games_modulus),
              games_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->zodiac_position,
                                                 Z::zpos(Positive::xh())),
                                     zodiac_modulus),
                         zodiac_modulus)});
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step_n(
    const unsigned int n,
    std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int rest = n - 1;
    return step_n(rest, step(std::move(s)));
  }
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::state_at_cell(std::shared_ptr<Z> cell) {
  return std::make_shared<EpochCellGlyphTraceCase::MechanismState>(
      MechanismState{cell, cell, cell, cell, cell, cell, cell});
}

__attribute__((pure)) EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::predict_moon_phase_from_state(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  std::shared_ptr<Z> phase_angle = BinInt::div(
      BinInt::mul(s->metonic_dial,
                  Z::zpos(Positive::xo(Positive::xo(
                      Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                          Positive::xi(Positive::xo(Positive::xh())))))))))),
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))))));
  return phase_from_angle(std::move(phase_angle));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::predict_olympiad_year(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  return BinInt::add(
      BinInt::modulo(s->games_dial,
                     Z::zpos(Positive::xo(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xh()));
}

__attribute__((pure)) EpochCellGlyphTraceCase::ZodiacSign
EpochCellGlyphTraceCase::predict_zodiac_sign(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  std::shared_ptr<Z> deg = BinInt::modulo(
      s->zodiac_position,
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
                              std::move(deg),
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
EpochCellGlyphTraceCase::glyph_at_cell(const std::shared_ptr<Z> &cell) {
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
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  if (std::holds_alternative<typename List<
          std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil>(
          es->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<
        std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons>(
        &es->v());
    unsigned int count_here = [&]() {
      switch (_m.d_a0->he_category) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        return 1u;
      }
      default: {
        return 0u;
      }
      }
    }();
    return (count_here + count_total_lunar(_m.d_a1));
  }
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::count_visible_total_lunar(
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  if (std::holds_alternative<typename List<
          std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil>(
          es->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<
        std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons>(
        &es->v());
    unsigned int count_here = [&]() {
      switch (_m.d_a0->he_category) {
      case EclipseCategory::e_EC_TOTALLUNAR: {
        if (_m.d_a0->he_visible_mediterranean) {
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
    return (count_here + count_visible_total_lunar(_m.d_a1));
  }
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::visible_series_checksum(
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  if (std::holds_alternative<typename List<
          std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil>(
          es->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<
        std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons>(
        &es->v());
    unsigned int term;
    if (_m.d_a0->he_visible_mediterranean) {
      term = BinInt::to_nat(BinInt::abs(_m.d_a0->he_saros_series));
    } else {
      term = 0u;
    }
    return (term + visible_series_checksum(_m.d_a1));
  }
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::months_from_epoch(
    const std::shared_ptr<Z> &epoch_year,
    const std::shared_ptr<Z> &eclipse_year,
    const std::shared_ptr<Z> &epoch_month,
    const std::shared_ptr<Z> &eclipse_month) {
  std::shared_ptr<Z> year_diff = BinInt::sub(epoch_year, eclipse_year);
  std::shared_ptr<Z> month_diff = BinInt::sub(eclipse_month, epoch_month);
  return BinInt::add(
      BinInt::mul(std::move(year_diff), Z::zpos(Positive::xo(Positive::xo(
                                            Positive::xi(Positive::xh()))))),
      std::move(month_diff));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::saros_cell(
    const std::shared_ptr<Z> &epoch_year, const std::shared_ptr<Z> &epoch_month,
    const std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse> &e) {
  std::shared_ptr<Z> months =
      months_from_epoch(epoch_year, e->he_year, epoch_month, e->he_month);
  return BinInt::modulo(
      std::move(months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::saros_dial_at_month(
    const std::shared_ptr<Z> &start_cell, const std::shared_ptr<Z> &months) {
  return BinInt::modulo(
      BinInt::add(start_cell, months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

std::shared_ptr<EpochCellGlyphTraceCase::EpochReading>
EpochCellGlyphTraceCase::build_epoch_reading(
    const std::shared_ptr<Z> &epoch_year, const std::shared_ptr<Z> &epoch_month,
    std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse> e) {
  std::shared_ptr<Z> cell = saros_cell(epoch_year, epoch_month, e);
  return std::make_shared<EpochCellGlyphTraceCase::EpochReading>(
      EpochReading{state_at_cell(cell), e, cell, glyph_at_cell(cell)});
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::reading_matches(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return category_matches_glyph(reading->reading_eclipse->he_category,
                                reading->reading_glyph);
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_phase_code(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return phase_code(predict_moon_phase_from_state(reading->reading_state));
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_zodiac_code(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return zodiac_code(predict_zodiac_sign(reading->reading_state));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::phase_code_after_steps(const unsigned int n) {
  return phase_code(predict_moon_phase_from_state(step_n(n, initial_state)));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::zodiac_code_after_steps(const unsigned int n) {
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

__attribute__((pure)) bool QArith_base::Qle_bool(const std::shared_ptr<Q> &x,
                                                 const std::shared_ptr<Q> &y) {
  return BinInt::leb(BinInt::mul(x->Qnum, Z::zpos(y->Qden)),
                     BinInt::mul(y->Qnum, Z::zpos(x->Qden)));
}
