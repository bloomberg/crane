#include "module_alias_target_handling.h"

Uint Little::double_(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::nil();
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d0(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d2(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d4(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d6(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d8(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::d0(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::d2(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::d4(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d6(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d8(succ_double(*a0));
  }
}

Uint Little::succ_double(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::d1(Uint::nil());
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d1(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d3(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d5(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d7(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d9(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::d1(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::d3(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::d5(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d7(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d9(succ_double(*a0));
  }
}

Uint0 Coq_Little::double_(const Uint0 &d) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return Uint0::nil0();
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Uint0::d10(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Uint0::d12(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Uint0::d14(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Uint0::d16(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Uint0::d18(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Uint0::da(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Uint0::dc(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Uint0::de(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Uint0::d10(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Uint0::d12(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Uint0::d14(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Uint0::d16(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Uint0::d18(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Uint0::da(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Uint0::dc(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Uint0::de(succ_double(*a0));
  }
}

Uint0 Coq_Little::succ_double(const Uint0 &d) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return Uint0::d11(Uint0::nil0());
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Uint0::d11(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Uint0::d13(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Uint0::d15(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Uint0::d17(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Uint0::d19(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Uint0::db(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Uint0::dd(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Uint0::df(double_(*a0));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Uint0::d11(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Uint0::d13(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Uint0::d15(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Uint0::d17(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Uint0::d19(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Uint0::db(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Uint0::dd(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Uint0::df(succ_double(*a0));
  }
}

unsigned int Pos::pred_double(unsigned int x) {
  if (x == 1u) {
    return 1u;
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * (2u * p) + 1u);
  } else {
    unsigned int p = x / 2u;
    return (2u * pred_double(p) + 1u);
  }
}

Pos::mask Pos::succ_double_mask(const Pos::mask &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x.v())) {
    return mask::ispos(1u);
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Pos::mask::IsPos>(x.v());
    return mask::ispos((2u * a0 + 1u));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_mask(const Pos::mask &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x.v())) {
    return mask::isnul();
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Pos::mask::IsPos>(x.v());
    return mask::ispos((2u * a0));
  } else {
    return mask::isneg();
  }
}

Pos::mask Pos::double_pred_mask(unsigned int x) {
  if (x == 1u) {
    return mask::isnul();
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return mask::ispos((2u * (2u * p)));
  } else {
    unsigned int p = x / 2u;
    return mask::ispos((2u * pred_double(p)));
  }
}

Pos::mask Pos::sub_mask(unsigned int x, unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return mask::isnul();
    } else if (y % 2u != 0u) {
      unsigned int _x = (y - 1u) / 2u;
      return mask::isneg();
    } else {
      unsigned int _x = y / 2u;
      return mask::isneg();
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return mask::ispos((2u * p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return double_mask(sub_mask(p, q));
    } else {
      unsigned int q = y / 2u;
      return succ_double_mask(sub_mask(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return mask::ispos(pred_double(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return double_mask(sub_mask(p, q));
    }
  }
}

Pos::mask Pos::sub_mask_carry(unsigned int x, unsigned int y) {
  if (x == 1u) {
    return mask::isneg();
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return mask::ispos(pred_double(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return double_mask(sub_mask(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return double_pred_mask(p);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    }
  }
}

Comparison Pos::compare_cont(Comparison r, unsigned int x, unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return r;
    } else if (y % 2u != 0u) {
      unsigned int _x = (y - 1u) / 2u;
      return Comparison::LT;
    } else {
      unsigned int _x = y / 2u;
      return Comparison::LT;
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return Comparison::GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(r, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(Comparison::GT, p, q);
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return Comparison::GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(Comparison::LT, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(r, p, q);
    }
  }
}

Comparison Pos::compare(unsigned int x0_, unsigned int x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

std::pair<unsigned int, Pos::mask> Pos::sqrtrem(unsigned int p) {
  if (p == 1u) {
    return std::make_pair(1u, mask::isnul());
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (p0 == 1u) {
      return std::make_pair(1u, mask::ispos((2u * 1u)));
    } else if (p0 % 2u != 0u) {
      unsigned int p1 = (p0 - 1u) / 2u;
      return sqrtrem_step([](unsigned int x) { return (2u * x + 1u); },
                          [](unsigned int x) { return (2u * x + 1u); },
                          sqrtrem(p1));
    } else {
      unsigned int p1 = p0 / 2u;
      return sqrtrem_step([](unsigned int x) { return (2u * x); },
                          [](unsigned int x) { return (2u * x + 1u); },
                          sqrtrem(p1));
    }
  } else {
    unsigned int p0 = p / 2u;
    if (p0 == 1u) {
      return std::make_pair(1u, mask::ispos(1u));
    } else if (p0 % 2u != 0u) {
      unsigned int p1 = (p0 - 1u) / 2u;
      return sqrtrem_step([](unsigned int x) { return (2u * x + 1u); },
                          [](unsigned int x) { return (2u * x); }, sqrtrem(p1));
    } else {
      unsigned int p1 = p0 / 2u;
      return sqrtrem_step([](unsigned int x) { return (2u * x); },
                          [](unsigned int x) { return (2u * x); }, sqrtrem(p1));
    }
  }
}

unsigned int Pos::sqrt(unsigned int p) { return sqrtrem(p).first; }

unsigned int Pos::Nsucc_double(unsigned int x) {
  if (x == 0u) {
    return 1u;
  } else {
    unsigned int p = x;
    return (2u * p + 1u);
  }
}

unsigned int Pos::Ndouble(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    return (2u * p);
  }
}

unsigned int Pos::lor(unsigned int p, unsigned int q) {
  if (p == 1u) {
    if (q == 1u) {
      return q;
    } else if (q % 2u != 0u) {
      unsigned int _x = (q - 1u) / 2u;
      return q;
    } else {
      unsigned int q0 = q / 2u;
      return (2u * q0 + 1u);
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (q == 1u) {
      return p;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return (2u * lor(p0, q0) + 1u);
    } else {
      unsigned int q0 = q / 2u;
      return (2u * lor(p0, q0) + 1u);
    }
  } else {
    unsigned int p0 = p / 2u;
    if (q == 1u) {
      return (2u * p0 + 1u);
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return (2u * lor(p0, q0) + 1u);
    } else {
      unsigned int q0 = q / 2u;
      return (2u * lor(p0, q0));
    }
  }
}

unsigned int Pos::land(unsigned int p, unsigned int q) {
  if (p == 1u) {
    if (q == 1u) {
      return 1u;
    } else if (q % 2u != 0u) {
      unsigned int _x = (q - 1u) / 2u;
      return 1u;
    } else {
      unsigned int _x = q / 2u;
      return 0u;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (q == 1u) {
      return 1u;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Nsucc_double(land(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Ndouble(land(p0, q0));
    }
  } else {
    unsigned int p0 = p / 2u;
    if (q == 1u) {
      return 0u;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Ndouble(land(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Ndouble(land(p0, q0));
    }
  }
}

unsigned int Pos::ldiff(unsigned int p, unsigned int q) {
  if (p == 1u) {
    if (q == 1u) {
      return 0u;
    } else if (q % 2u != 0u) {
      unsigned int _x = (q - 1u) / 2u;
      return 0u;
    } else {
      unsigned int _x = q / 2u;
      return 1u;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (q == 1u) {
      return (2u * p0);
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Ndouble(ldiff(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Nsucc_double(ldiff(p0, q0));
    }
  } else {
    unsigned int p0 = p / 2u;
    if (q == 1u) {
      return p;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Ndouble(ldiff(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Ndouble(ldiff(p0, q0));
    }
  }
}

unsigned int Pos::lxor(unsigned int p, unsigned int q) {
  if (p == 1u) {
    if (q == 1u) {
      return 0u;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return (2u * q0);
    } else {
      unsigned int q0 = q / 2u;
      return (2u * q0 + 1u);
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (q == 1u) {
      return (2u * p0);
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Ndouble(lxor(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Nsucc_double(lxor(p0, q0));
    }
  } else {
    unsigned int p0 = p / 2u;
    if (q == 1u) {
      return (2u * p0 + 1u);
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return Nsucc_double(lxor(p0, q0));
    } else {
      unsigned int q0 = q / 2u;
      return Ndouble(lxor(p0, q0));
    }
  }
}

unsigned int Coq_Pos::add_carry(unsigned int x, unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return (2u * 1u + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * (q + 1u) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * (q + 1u));
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return (2u * (p + 1u) + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * add_carry(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return (2u * (p + 1u));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return (2u * (p + q) + 1u);
    }
  }
}

unsigned int Coq_Pos::pred_double(unsigned int x) {
  if (x == 1u) {
    return 1u;
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * (2u * p) + 1u);
  } else {
    unsigned int p = x / 2u;
    return (2u * pred_double(p) + 1u);
  }
}

unsigned int Coq_Pos::pred_N(unsigned int x) {
  if (x == 1u) {
    return 0u;
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * p);
  } else {
    unsigned int p = x / 2u;
    return pred_double(p);
  }
}

Comparison Coq_Pos::compare_cont(Comparison r, unsigned int x, unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return r;
    } else if (y % 2u != 0u) {
      unsigned int _x = (y - 1u) / 2u;
      return Comparison::LT;
    } else {
      unsigned int _x = y / 2u;
      return Comparison::LT;
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return Comparison::GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(r, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(Comparison::GT, p, q);
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return Comparison::GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(Comparison::LT, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(r, p, q);
    }
  }
}

Comparison Coq_Pos::compare(unsigned int x0_, unsigned int x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

unsigned int Coq_Pos::pow(unsigned int x, unsigned int x0_) {
  return iter<unsigned int>(
      [=](unsigned int _x0) -> unsigned int { return (x * _x0); }, 1u, x0_);
}

unsigned int Coq_Pos::square(unsigned int p) {
  if (p == 1u) {
    return 1u;
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    return (2u * (2u * (square(p0) + p0)) + 1u);
  } else {
    unsigned int p0 = p / 2u;
    return (2u * (2u * square(p0)));
  }
}

uint64_t Coq_Pos::size_nat(unsigned int p) {
  if (p == 1u) {
    return UINT64_C(1);
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    return (size_nat(p0) + 1);
  } else {
    unsigned int p0 = p / 2u;
    return (size_nat(p0) + 1);
  }
}

unsigned int Coq_Pos::size(unsigned int p) {
  if (p == 1u) {
    return 1u;
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    return (size(p0) + 1u);
  } else {
    unsigned int p0 = p / 2u;
    return (size(p0) + 1u);
  }
}

unsigned int Coq_Pos::gcdn(uint64_t n, unsigned int a, unsigned int b) {
  if (n <= 0) {
    return 1u;
  } else {
    uint64_t n0 = n - 1;
    if (a == 1u) {
      return 1u;
    } else if (a % 2u != 0u) {
      unsigned int a_ = (a - 1u) / 2u;
      if (b == 1u) {
        return 1u;
      } else if (b % 2u != 0u) {
        unsigned int b_ = (b - 1u) / 2u;
        switch (compare(a_, b_)) {
        case Comparison::EQ: {
          return a;
        }
        case Comparison::LT: {
          return gcdn(n0, (b_ - a_), a);
        }
        case Comparison::GT: {
          return gcdn(n0, (a_ - b_), b);
        }
        default:
          std::unreachable();
        }
      } else {
        unsigned int b0 = b / 2u;
        return gcdn(n0, a, b0);
      }
    } else {
      unsigned int a0 = a / 2u;
      if (b == 1u) {
        return 1u;
      } else if (b % 2u != 0u) {
        unsigned int _x = (b - 1u) / 2u;
        return gcdn(n0, a0, b);
      } else {
        unsigned int b0 = b / 2u;
        return (2u * gcdn(n0, a0, b0));
      }
    }
  }
}

unsigned int Coq_Pos::gcd(unsigned int a, unsigned int b) {
  return gcdn((size_nat(a) + size_nat(b)), a, b);
}

std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
Coq_Pos::ggcdn(uint64_t n, unsigned int a, unsigned int b) {
  if (n <= 0) {
    return std::make_pair(1u, std::make_pair(a, b));
  } else {
    uint64_t n0 = n - 1;
    if (a == 1u) {
      return std::make_pair(1u, std::make_pair(1u, b));
    } else if (a % 2u != 0u) {
      unsigned int a_ = (a - 1u) / 2u;
      if (b == 1u) {
        return std::make_pair(1u, std::make_pair(a, 1u));
      } else if (b % 2u != 0u) {
        unsigned int b_ = (b - 1u) / 2u;
        switch (compare(a_, b_)) {
        case Comparison::EQ: {
          return std::make_pair(a, std::make_pair(1u, 1u));
        }
        case Comparison::LT: {
          auto [g, p] = ggcdn(n0, (b_ - a_), a);
          const auto &[ba, aa] = p;
          return std::make_pair(g, std::make_pair(aa, (aa + (2u * ba))));
          break;
        }
        case Comparison::GT: {
          auto [g, p] = ggcdn(n0, (a_ - b_), std::move(b));
          const auto &[ab, bb] = p;
          return std::make_pair(g, std::make_pair((bb + (2u * ab)), bb));
          break;
        }
        default:
          std::unreachable();
        }
      } else {
        unsigned int b0 = b / 2u;
        auto [g, p] = ggcdn(n0, a, b0);
        const auto &[aa, bb] = p;
        return std::make_pair(g, std::make_pair(std::move(p.first), (2u * bb)));
      }
    } else {
      unsigned int a0 = a / 2u;
      if (b == 1u) {
        return std::make_pair(1u, std::make_pair(a, 1u));
      } else if (b % 2u != 0u) {
        unsigned int _x = (b - 1u) / 2u;
        auto [g, p] = ggcdn(n0, a0, std::move(b));
        const auto &[aa, bb] = p;
        return std::make_pair(g, std::make_pair((2u * aa), bb));
      } else {
        unsigned int b0 = b / 2u;
        auto [g, p] = ggcdn(n0, a0, b0);
        return std::make_pair((2u * g), p);
      }
    }
  }
}

std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
Coq_Pos::ggcd(unsigned int a, unsigned int b) {
  return ggcdn((size_nat(a) + size_nat(b)), a, b);
}

unsigned int Coq_Pos::shiftl(unsigned int p, unsigned int n) {
  if (n == 0u) {
    return p;
  } else {
    unsigned int n0 = n;
    return iter<unsigned int>([](unsigned int x) { return (2u * x); }, p, n0);
  }
}

bool Coq_Pos::testbit_nat(unsigned int p, uint64_t n) {
  if (p == 1u) {
    if (n <= 0) {
      return true;
    } else {
      uint64_t _x = n - 1;
      return false;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (n <= 0) {
      return true;
    } else {
      uint64_t n_ = n - 1;
      return testbit_nat(p0, n_);
    }
  } else {
    unsigned int p0 = p / 2u;
    if (n <= 0) {
      return false;
    } else {
      uint64_t n_ = n - 1;
      return testbit_nat(p0, n_);
    }
  }
}

bool Coq_Pos::testbit(unsigned int p, unsigned int n) {
  if (p == 1u) {
    if (n == 0u) {
      return true;
    } else {
      unsigned int _x = n;
      return false;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (n == 0u) {
      return true;
    } else {
      unsigned int n0 = n;
      return testbit(p0, pred_N(n0));
    }
  } else {
    unsigned int p0 = p / 2u;
    if (n == 0u) {
      return false;
    } else {
      unsigned int n0 = n;
      return testbit(p0, pred_N(n0));
    }
  }
}

unsigned int Coq_Pos::of_uint_acc(const Uint &d, unsigned int acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return of_uint_acc(*a0, ((2u * (2u * (2u * 1u) + 1u)) * acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return of_uint_acc(*a0, (1u + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return of_uint_acc(*a0, ((2u * 1u) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return of_uint_acc(*a0,
                       ((2u * 1u + 1u) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return of_uint_acc(
        *a0, ((2u * (2u * 1u)) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return of_uint_acc(
        *a0, ((2u * (2u * 1u) + 1u) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return of_uint_acc(
        *a0, ((2u * (2u * 1u + 1u)) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return of_uint_acc(*a0, ((2u * (2u * 1u + 1u) + 1u) +
                             ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return of_uint_acc(
        *a0, ((2u * (2u * (2u * 1u))) + ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return of_uint_acc(*a0, ((2u * (2u * (2u * 1u)) + 1u) +
                             ((2u * (2u * (2u * 1u) + 1u)) * acc)));
  }
}

unsigned int Coq_Pos::of_uint(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return 0u;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return of_uint(*a0);
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return of_uint_acc(*a0, 1u);
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return of_uint_acc(*a0, (2u * 1u));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return of_uint_acc(*a0, (2u * 1u + 1u));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return of_uint_acc(*a0, (2u * (2u * 1u)));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return of_uint_acc(*a0, (2u * (2u * 1u) + 1u));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return of_uint_acc(*a0, (2u * (2u * 1u + 1u)));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return of_uint_acc(*a0, (2u * (2u * 1u + 1u) + 1u));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return of_uint_acc(*a0, (2u * (2u * (2u * 1u))));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return of_uint_acc(*a0, (2u * (2u * (2u * 1u)) + 1u));
  }
}

unsigned int Coq_Pos::of_hex_uint_acc(const Uint0 &d, unsigned int acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * (2u * 1u)))) * acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return of_hex_uint_acc(*a0, (1u + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return of_hex_uint_acc(
        *a0, ((2u * 1u) + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return of_hex_uint_acc(
        *a0, ((2u * 1u + 1u) + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return of_hex_uint_acc(
        *a0, ((2u * (2u * 1u)) + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return of_hex_uint_acc(
        *a0, ((2u * (2u * 1u) + 1u) + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return of_hex_uint_acc(
        *a0, ((2u * (2u * 1u + 1u)) + ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * 1u + 1u) + 1u) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u))) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u)) + 1u) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u) + 1u)) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u) + 1u) + 1u) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u + 1u))) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u + 1u)) + 1u) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u + 1u) + 1u)) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return of_hex_uint_acc(*a0, ((2u * (2u * (2u * 1u + 1u) + 1u) + 1u) +
                                 ((2u * (2u * (2u * (2u * 1u)))) * acc)));
  }
}

unsigned int Coq_Pos::of_hex_uint(const Uint0 &d) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return 0u;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return of_hex_uint(*a0);
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return of_hex_uint_acc(*a0, 1u);
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return of_hex_uint_acc(*a0, (2u * 1u));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return of_hex_uint_acc(*a0, (2u * 1u + 1u));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * 1u)));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * 1u) + 1u));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * 1u + 1u)));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * 1u + 1u) + 1u));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u))));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u)) + 1u));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u) + 1u)));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u) + 1u) + 1u));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u + 1u))));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u + 1u)) + 1u));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u + 1u) + 1u)));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return of_hex_uint_acc(*a0, (2u * (2u * (2u * 1u + 1u) + 1u) + 1u));
  }
}

Uint Coq_Pos::to_little_uint(unsigned int p) {
  if (p == 1u) {
    return Uint::d1(Uint::nil());
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    return Little::succ_double(to_little_uint(p0));
  } else {
    unsigned int p0 = p / 2u;
    return Little::double_(to_little_uint(p0));
  }
}

Uint Coq_Pos::to_uint(unsigned int p) { return to_little_uint(p).rev(); }

Uint0 Coq_Pos::to_little_hex_uint(unsigned int p) {
  if (p == 1u) {
    return Uint0::d11(Uint0::nil0());
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    return Coq_Little::succ_double(to_little_hex_uint(p0));
  } else {
    unsigned int p0 = p / 2u;
    return Coq_Little::double_(to_little_hex_uint(p0));
  }
}

Uint0 Coq_Pos::to_hex_uint(unsigned int p) {
  return to_little_hex_uint(p).rev0();
}

bool Coq_Pos::eq_dec(unsigned int p, unsigned int x0) {
  if (p == 1u) {
    if (x0 == 1u) {
      return true;
    } else if (x0 % 2u != 0u) {
      unsigned int _x = (x0 - 1u) / 2u;
      return false;
    } else {
      unsigned int _x = x0 / 2u;
      return false;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (x0 == 1u) {
      return false;
    } else if (x0 % 2u != 0u) {
      unsigned int p1 = (x0 - 1u) / 2u;
      if (eq_dec(p0, p1)) {
        return true;
      } else {
        return false;
      }
    } else {
      unsigned int _x = x0 / 2u;
      return false;
    }
  } else {
    unsigned int p0 = p / 2u;
    if (x0 == 1u) {
      return false;
    } else if (x0 % 2u != 0u) {
      unsigned int _x = (x0 - 1u) / 2u;
      return false;
    } else {
      unsigned int p1 = x0 / 2u;
      if (eq_dec(p0, p1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

unsigned int N::succ_pos(unsigned int n) {
  if (n == 0u) {
    return 1u;
  } else {
    unsigned int p = n;
    return (p + 1u);
  }
}

Comparison N::compare(unsigned int n, unsigned int m) {
  if (n == 0u) {
    if (m == 0u) {
      return Comparison::EQ;
    } else {
      unsigned int _x = m;
      return Comparison::LT;
    }
  } else {
    unsigned int n_ = n;
    if (m == 0u) {
      return Comparison::GT;
    } else {
      unsigned int m_ = m;
      return Pos::compare(n_, m_);
    }
  }
}

std::pair<unsigned int, unsigned int> N::pos_div_eucl(unsigned int a,
                                                      unsigned int b) {
  if (a == 1u) {
    if (b == 0u) {
      return std::make_pair(0u, 1u);
    } else {
      unsigned int p = b;
      if (p == 1u) {
        return std::make_pair(1u, 0u);
      } else if (p % 2u != 0u) {
        unsigned int _x = (p - 1u) / 2u;
        return std::make_pair(0u, 1u);
      } else {
        unsigned int _x = p / 2u;
        return std::make_pair(0u, 1u);
      }
    }
  } else if (a % 2u != 0u) {
    unsigned int a_ = (a - 1u) / 2u;
    auto [q, r] = pos_div_eucl(a_, b);
    unsigned int r_ = (r * 2u + 1u);
    if (b <= r_) {
      return std::make_pair((q * 2u + 1u), (r_ >= b ? r_ - b : 0u));
    } else {
      return std::make_pair((q * 2u), r_);
    }
  } else {
    unsigned int a_ = a / 2u;
    auto [q, r] = pos_div_eucl(a_, b);
    unsigned int r_ = (r * 2u);
    if (b <= r_) {
      return std::make_pair((q * 2u + 1u), (r_ >= b ? r_ - b : 0u));
    } else {
      return std::make_pair((q * 2u), r_);
    }
  }
}

unsigned int N::lor(unsigned int n, unsigned int m) {
  if (n == 0u) {
    return m;
  } else {
    unsigned int p = n;
    if (m == 0u) {
      return n;
    } else {
      unsigned int q = m;
      return Pos::lor(p, q);
    }
  }
}

unsigned int N::land(unsigned int n, unsigned int m) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    if (m == 0u) {
      return 0u;
    } else {
      unsigned int q = m;
      return Pos::land(p, q);
    }
  }
}

unsigned int N::ldiff(unsigned int n, unsigned int m) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    if (m == 0u) {
      return n;
    } else {
      unsigned int q = m;
      return Pos::ldiff(p, q);
    }
  }
}

unsigned int N::lxor(unsigned int n, unsigned int m) {
  if (n == 0u) {
    return m;
  } else {
    unsigned int p = n;
    if (m == 0u) {
      return n;
    } else {
      unsigned int q = m;
      return Pos::lxor(p, q);
    }
  }
}

unsigned int N::div2(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p0 = n;
    if (p0 == 1u) {
      return 0u;
    } else if (p0 % 2u != 0u) {
      unsigned int p = (p0 - 1u) / 2u;
      return p;
    } else {
      unsigned int p = p0 / 2u;
      return p;
    }
  }
}

bool N::even(unsigned int n) {
  if (n == 0u) {
    return true;
  } else {
    unsigned int p = n;
    if (p == 1u) {
      return false;
    } else if (p % 2u != 0u) {
      unsigned int _x = (p - 1u) / 2u;
      return false;
    } else {
      unsigned int _x = p / 2u;
      return true;
    }
  }
}

bool N::odd(unsigned int n) { return !(even(n)); }

unsigned int N::pow(unsigned int n, unsigned int p) {
  if (p == 0u) {
    return 1u;
  } else {
    unsigned int p0 = p;
    if (n == 0u) {
      return 0u;
    } else {
      unsigned int q = n;
      return Coq_Pos::pow(q, p0);
    }
  }
}

unsigned int N::square(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    return Coq_Pos::square(p);
  }
}

unsigned int N::log2(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p0 = n;
    if (p0 == 1u) {
      return 0u;
    } else if (p0 % 2u != 0u) {
      unsigned int p = (p0 - 1u) / 2u;
      return Coq_Pos::size(p);
    } else {
      unsigned int p = p0 / 2u;
      return Coq_Pos::size(p);
    }
  }
}

unsigned int N::size(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    return Coq_Pos::size(p);
  }
}

uint64_t N::size_nat(unsigned int n) {
  if (n == 0u) {
    return UINT64_C(0);
  } else {
    unsigned int p = n;
    return Coq_Pos::size_nat(p);
  }
}

std::pair<unsigned int, unsigned int> N::div_eucl(unsigned int a,
                                                  unsigned int b) {
  if (a == 0u) {
    return std::make_pair(0u, 0u);
  } else {
    unsigned int na = a;
    if (b == 0u) {
      return std::make_pair(0u, a);
    } else {
      unsigned int _x = b;
      return pos_div_eucl(na, b);
    }
  }
}

unsigned int N::gcd(unsigned int a, unsigned int b) {
  if (a == 0u) {
    return b;
  } else {
    unsigned int p = a;
    if (b == 0u) {
      return a;
    } else {
      unsigned int q = b;
      return Coq_Pos::gcd(p, q);
    }
  }
}

std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
N::ggcd(unsigned int a, unsigned int b) {
  if (a == 0u) {
    return std::make_pair(std::move(b), std::make_pair(0u, 1u));
  } else {
    unsigned int p = a;
    if (b == 0u) {
      return std::make_pair(a, std::make_pair(1u, 0u));
    } else {
      unsigned int q = b;
      auto [g, p0] = Coq_Pos::ggcd(p, q);
      const auto &[aa, bb] = p0;
      return std::make_pair(g, std::make_pair(aa, bb));
    }
  }
}

std::pair<unsigned int, unsigned int> N::sqrtrem(unsigned int n) {
  if (n == 0u) {
    return std::make_pair(0u, 0u);
  } else {
    unsigned int p = n;
    auto [s, m] = Pos::sqrtrem(p);
    if (std::holds_alternative<typename Pos::mask::IsPos>(m.v_mut())) {
      auto &[a0] = std::get<typename Pos::mask::IsPos>(m.v_mut());
      return std::make_pair(s, std::move(a0));
    } else {
      return std::make_pair(s, 0u);
    }
  }
}

unsigned int N::sqrt(unsigned int n) {
  if (n == 0u) {
    return 0u;
  } else {
    unsigned int p = n;
    return Pos::sqrt(p);
  }
}

unsigned int N::shiftl_nat(unsigned int a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    return (shiftl_nat(a, n0) * 2u);
  }
}

unsigned int N::shiftr_nat(unsigned int a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    return div2(shiftr_nat(a, n0));
  }
}

unsigned int N::shiftl(unsigned int a, unsigned int n) {
  if (a == 0u) {
    return 0u;
  } else {
    unsigned int a0 = a;
    return Coq_Pos::shiftl(a0, n);
  }
}

unsigned int N::shiftr(unsigned int a, unsigned int n) {
  if (n == 0u) {
    return a;
  } else {
    unsigned int p = n;
    return Pos::template iter<unsigned int>(div2, a, p);
  }
}

bool N::testbit_nat(unsigned int a, uint64_t x0_) {
  if (a == 0u) {
    return false;
  } else {
    unsigned int p = a;
    return Coq_Pos::testbit_nat(p, x0_);
  }
}

bool N::testbit(unsigned int a, unsigned int n) {
  if (a == 0u) {
    return false;
  } else {
    unsigned int p = a;
    return Coq_Pos::testbit(p, n);
  }
}

unsigned int N::of_uint(const Uint &x0_) { return Coq_Pos::of_uint(x0_); }

unsigned int N::of_hex_uint(const Uint0 &x0_) {
  return Coq_Pos::of_hex_uint(x0_);
}

unsigned int N::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return of_hex_uint(u);
  }
}

std::optional<unsigned int> N::of_int(const Signed_int &d) {
  auto &&_sv = d.norm();
  if (std::holds_alternative<typename Signed_int::Pos>(_sv.v())) {
    const auto &[d1] = std::get<typename Signed_int::Pos>(_sv.v());
    return std::make_optional<unsigned int>(Coq_Pos::of_uint(d1));
  } else {
    return std::optional<unsigned int>();
  }
}

std::optional<unsigned int> N::of_hex_int(const Signed_int0 &d) {
  auto &&_sv = d.norm0();
  if (std::holds_alternative<typename Signed_int0::Pos0>(_sv.v())) {
    const auto &[d1] = std::get<typename Signed_int0::Pos0>(_sv.v());
    return std::make_optional<unsigned int>(Coq_Pos::of_hex_uint(d1));
  } else {
    return std::optional<unsigned int>();
  }
}

std::optional<unsigned int> N::of_num_int(const Signed_int1 &d) {
  if (std::holds_alternative<typename Signed_int1::IntDecimal>(d.v())) {
    const auto &[i] = std::get<typename Signed_int1::IntDecimal>(d.v());
    return of_int(i);
  } else {
    const auto &[i] = std::get<typename Signed_int1::IntHexadecimal>(d.v());
    return of_hex_int(i);
  }
}

Uint N::to_uint(unsigned int n) {
  if (n == 0u) {
    return Uint::d0(Uint::nil());
  } else {
    unsigned int p = n;
    return Coq_Pos::to_uint(p);
  }
}

Uint0 N::to_hex_uint(unsigned int n) {
  if (n == 0u) {
    return Uint0::d10(Uint0::nil0());
  } else {
    unsigned int p = n;
    return Coq_Pos::to_hex_uint(p);
  }
}

Uint1 N::to_num_uint(unsigned int n) { return Uint1::uintdecimal(to_uint(n)); }

Uint1 N::to_num_hex_uint(unsigned int n) {
  return Uint1::uinthexadecimal(to_hex_uint(n));
}

Signed_int N::to_int(unsigned int n) { return Signed_int::pos(to_uint(n)); }

Signed_int0 N::to_hex_int(unsigned int n) {
  return Signed_int0::pos0(to_hex_uint(n));
}

Signed_int1 N::to_num_int(unsigned int n) {
  return Signed_int1::intdecimal(to_int(n));
}

Signed_int1 N::to_num_hex_int(unsigned int n) {
  return Signed_int1::inthexadecimal(to_hex_int(n));
}

bool N::eq_dec(unsigned int n, unsigned int m) {
  if (n == 0u) {
    if (m == 0u) {
      return true;
    } else {
      unsigned int _x = m;
      return false;
    }
  } else {
    unsigned int p = n;
    if (m == 0u) {
      return false;
    } else {
      unsigned int p0 = m;
      if (Coq_Pos::eq_dec(p, p0)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

Sumor<Sig<unsigned int>> N::discr(unsigned int n) {
  if (n == 0u) {
    return Sumor<Sig<unsigned int>>::inright();
  } else {
    unsigned int p = n;
    return Sumor<Sig<unsigned int>>::inleft(Sig<unsigned int>::exist(p));
  }
}

Reflect N::leb_spec0(unsigned int x, unsigned int y) {
  return Bool::iff_reflect(x <= y);
}

Reflect N::ltb_spec0(unsigned int x, unsigned int y) {
  return Bool::iff_reflect(x < y);
}

bool N::Private_Dec::max_dec(unsigned int n, unsigned int m) {
  return max_case<bool>(
      n, m,
      [](unsigned int, unsigned int, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool N::Private_Dec::min_dec(unsigned int n, unsigned int m) {
  return min_case<bool>(
      n, m,
      [](unsigned int, unsigned int, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool N::max_dec(unsigned int x0_, unsigned int x1_) {
  return Private_Dec::max_dec(x0_, x1_);
}

bool N::min_dec(unsigned int x0_, unsigned int x1_) {
  return Private_Dec::min_dec(x0_, x1_);
}

unsigned int N::sqrt_up(unsigned int a) {
  switch (compare(0u, a)) {
  case Comparison::LT: {
    return (sqrt((a == 0u ? 0u : a - 1u)) + 1u);
  }
  default: {
    return 0u;
  }
  }
}

unsigned int N::log2_up(unsigned int a) {
  switch (compare(1u, a)) {
  case Comparison::LT: {
    return (log2((a == 0u ? 0u : a - 1u)) + 1u);
  }
  default: {
    return 0u;
  }
  }
}

unsigned int N::Private_NLcmProp::lcm(unsigned int a, unsigned int b) {
  auto &&_once1 = gcd(a, b);
  return (a * (_once1 == 0u ? 0u : b / _once1));
}

unsigned int N::lcm(unsigned int a, unsigned int b) {
  auto &&_once1 = gcd(a, b);
  return (a * (_once1 == 0u ? 0u : b / _once1));
}

Reflect N::eqb_spec(unsigned int x, unsigned int y) {
  return Bool::iff_reflect(x == y);
}

unsigned int N::b2n(bool b) {
  if (b) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int N::setbit(unsigned int a, unsigned int n) {
  return lor(a, shiftl(1u, n));
}

unsigned int N::clearbit(unsigned int a, unsigned int n) {
  return ldiff(a, shiftl(1u, n));
}

unsigned int N::ones(unsigned int n) {
  auto &&_once1 = shiftl(1u, n);
  return (_once1 == 0u ? 0u : _once1 - 1u);
}

unsigned int N::lnot(unsigned int a, unsigned int n) {
  return lxor(a, ones(n));
}

CompareSpecT Datatypes::CompareSpec2Type(Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return CompareSpecT::COMPEQT;
  }
  case Comparison::LT: {
    return CompareSpecT::COMPLTT;
  }
  case Comparison::GT: {
    return CompareSpecT::COMPGTT;
  }
  default:
    std::unreachable();
  }
}

Reflect Bool::iff_reflect(bool b) {
  if (b) {
    return Reflect::REFLECTT;
  } else {
    return Reflect::REFLECTF;
  }
}
