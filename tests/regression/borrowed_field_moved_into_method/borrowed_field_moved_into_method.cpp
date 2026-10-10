#include "borrowed_field_moved_into_method.h"

Positive Coq_Pos::succ(const Positive &x) {
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

Positive Coq_Pos::add(const Positive &x, const Positive &y) {
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

Positive Coq_Pos::add_carry(const Positive &x, const Positive &y) {
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

Positive Coq_Pos::mul(const Positive &x, Positive y) {
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

Pos::mask Pos::succ_double_mask(const Pos::mask &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x.v())) {
    return mask::ispos(Positive::xh());
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Pos::mask::IsPos>(x.v());
    return mask::ispos(Positive::xi(a0));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_mask(const Pos::mask &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x.v())) {
    return mask::isnul();
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Pos::mask::IsPos>(x.v());
    return mask::ispos(Positive::xo(a0));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_pred_mask(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return mask::ispos(Positive::xo(Positive::xo(*a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return mask::ispos(Positive::xo(pred_double(*a0)));
  } else {
    return mask::isnul();
  }
}

Pos::mask Pos::sub_mask(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return mask::isnul();
    } else {
      return mask::isneg();
    }
  }
}

Pos::mask Pos::sub_mask_carry(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else {
      return double_pred_mask(*a0);
    }
  } else {
    return mask::isneg();
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

Comparison Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
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

Positive Pos::of_succ_nat(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return Positive::xh();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    return succ(of_succ_nat(*a0));
  }
}

N BinNat::succ_double(const N &x) {
  if (std::holds_alternative<typename N::N0>(x.v())) {
    return N::npos(Positive::xh());
  } else {
    const auto &[a0] = std::get<typename N::Npos>(x.v());
    return N::npos(Positive::xi(a0));
  }
}

N BinNat::double_(const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return N::npos(Positive::xo(a0));
  }
}

N BinNat::sub(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return n;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      auto &&_sv1 = Pos::sub_mask(a0, a00);
      if (std::holds_alternative<typename Pos::mask::IsPos>(_sv1.v())) {
        const auto &[a01] = std::get<typename Pos::mask::IsPos>(_sv1.v());
        return N::npos(a01);
      } else {
        return N::n0();
      }
    }
  }
}

Comparison BinNat::compare(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return Pos::compare(a0, a00);
    }
  }
}

bool BinNat::leb(const N &x, const N &y) {
  switch (BinNat::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

std::pair<N, N> BinNat::pos_div_eucl(const Positive &a, const N &b) {
  if (std::holds_alternative<typename Positive::XI>(a.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(a.v());
    auto [q, r] = BinNat::pos_div_eucl(*a0, b);
    N r_ = BinNat::succ_double(std::move(r));
    if (BinNat::leb(b, r_)) {
      return std::make_pair(BinNat::succ_double(std::move(q)),
                            BinNat::sub(std::move(r_), b));
    } else {
      return std::make_pair(BinNat::double_(std::move(q)), std::move(r_));
    }
  } else if (std::holds_alternative<typename Positive::XO>(a.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(a.v());
    auto [q, r] = BinNat::pos_div_eucl(*a0, b);
    N r_ = BinNat::double_(std::move(r));
    if (BinNat::leb(b, r_)) {
      return std::make_pair(BinNat::succ_double(std::move(q)),
                            BinNat::sub(std::move(r_), b));
    } else {
      return std::make_pair(BinNat::double_(std::move(q)), std::move(r_));
    }
  } else {
    if (std::holds_alternative<typename N::N0>(b.v())) {
      return std::make_pair(N::n0(), N::npos(Positive::xh()));
    } else {
      const auto &[a00] = std::get<typename N::Npos>(b.v());
      if (std::holds_alternative<typename Positive::XH>(a00.v())) {
        return std::make_pair(N::npos(Positive::xh()), N::n0());
      } else {
        return std::make_pair(N::n0(), N::npos(Positive::xh()));
      }
    }
  }
}

N BinNat::mul(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return N::n0();
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return N::npos(Coq_Pos::mul(a0, a00));
    }
  }
}

std::pair<N, N> BinNat::div_eucl(const N &a, const N &b) {
  if (std::holds_alternative<typename N::N0>(a.v())) {
    return std::make_pair(N::n0(), N::n0());
  } else {
    const auto &[a0] = std::get<typename N::Npos>(a.v());
    if (std::holds_alternative<typename N::N0>(b.v())) {
      return std::make_pair(N::n0(), a);
    } else {
      return BinNat::pos_div_eucl(a0, b);
    }
  }
}

N BinNat::div(const N &a, const N &b) { return BinNat::div_eucl(a, b).first; }

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

Z BinInt::add(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::add(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return BinInt::pos_sub(a0, a00);
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return BinInt::pos_sub(a00, a0);
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::add(a0, a00));
    }
  }
}

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

Z BinInt::of_nat(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return Z::z0();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    return Z::zpos(Pos::of_succ_nat(*a0));
  }
}

Z BinInt::of_N(const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return Z::z0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return Z::zpos(a0);
  }
}

N BorrowedFieldMovedIntoMethod::sz(const BfmTypes::ty &t) {
  if (std::holds_alternative<typename BfmTypes::ty::TB>(t.v())) {
    const auto &[n0] = std::get<typename BfmTypes::ty::TB>(t.v());
    return BinNat::div(
        N::npos(n0),
        N::npos(Positive::xo(Positive::xo(Positive::xo(Positive::xh())))));
  } else if (std::holds_alternative<typename BfmTypes::ty::TS>(t.v())) {
    return N::n0();
  } else {
    const auto &[vector, sz0, t1] = std::get<typename BfmTypes::ty::TA>(t.v());
    return BinNat::mul(sz0, sz(*t1));
  }
}

Z BorrowedFieldMovedIntoMethod::get(const std::optional<Z> &o) {
  if (o.has_value()) {
    const Z &z = *o;
    return z;
  } else {
    return Z::z0();
  }
}

/// Each walk is 3 * 8 = 24.
bool BorrowedFieldMovedIntoMethod::check(std::monostate) {
  return BinInt::eqb(
      BinInt::add(get(walk<BorrowedFieldMovedIntoMethod::SizeI>(
                      arr, Z::z0(),
                      List<Nat>::cons(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                      List<Nat>::nil()))),
                  get(walk<BorrowedFieldMovedIntoMethod::SizeI>(
                      arr, Z::z0(),
                      List<Nat>::cons(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                      List<Nat>::nil())))),
      Z::zpos(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xi(Positive::xh())))))));
}
