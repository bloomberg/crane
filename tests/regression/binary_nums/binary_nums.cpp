#include "binary_nums.h"

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

N Pos::pred_N(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return N::npos(Positive::xo(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return N::npos(pred_double(*a0));
  } else {
    return N::n0();
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

Comparison Pos::compare(const Positive &_x0, const Positive &_x1) {
  return compare_cont(Comparison::EQ, _x0, _x1);
}

unsigned int Pos::to_nat(const Positive &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

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

unsigned int Coq_Pos::to_nat(const Positive &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

N BinNat::sub(N n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v_mut())) {
    return N::n0();
  } else {
    auto &[a0] = std::get<typename N::Npos>(n.v_mut());
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

N BinNat::pred(const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return Pos::pred_N(a0);
  }
}

N BinNat::add(N n, N m) {
  if (std::holds_alternative<typename N::N0>(n.v_mut())) {
    return m;
  } else {
    auto &[a0] = std::get<typename N::Npos>(n.v_mut());
    if (std::holds_alternative<typename N::N0>(m.v_mut())) {
      return n;
    } else {
      auto &[a00] = std::get<typename N::Npos>(m.v_mut());
      return N::npos(Coq_Pos::add(std::move(a0), std::move(a00)));
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

unsigned int BinNat::to_nat(const N &a) {
  if (std::holds_alternative<typename N::N0>(a.v())) {
    return 0u;
  } else {
    const auto &[a0] = std::get<typename N::Npos>(a.v());
    return Pos::to_nat(a0);
  }
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

unsigned int BinInt::to_nat(const Z &z) {
  if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Pos::to_nat(a0);
  } else {
    return 0u;
  }
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

N BinaryNums::n_max(N a, N b) {
  switch (BinNat::compare(a, b)) {
  case Comparison::LT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

Z BinaryNums::z_sign(const Z &z) {
  if (std::holds_alternative<typename Z::Z0>(z.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    return Z::zpos(Positive::xh());
  } else {
    return Z::zneg(Positive::xh());
  }
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
