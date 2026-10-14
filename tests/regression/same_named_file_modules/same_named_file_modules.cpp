#include "same_named_file_modules.h"

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

Positive Coq_Pos::pred_double(const Positive &x) {
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

N Coq_Pos::pred_N(const Positive &x) {
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

Coq_Pos::mask Coq_Pos::double_pred_mask(const Positive &x) {
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

Coq_Pos::mask Coq_Pos::sub_mask(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return sub_mask(*a0, *a00).double_mask();
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return sub_mask(*a0, *a00).succ_double_mask();
    } else {
      return mask::ispos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return sub_mask_carry(*a0, *a00).succ_double_mask();
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return sub_mask(*a0, *a00).double_mask();
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

Coq_Pos::mask Coq_Pos::sub_mask_carry(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return sub_mask_carry(*a0, *a00).succ_double_mask();
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return sub_mask(*a0, *a00).double_mask();
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return sub_mask_carry(*a0, *a00).double_mask();
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return sub_mask_carry(*a0, *a00).succ_double_mask();
    } else {
      return double_pred_mask(*a0);
    }
  } else {
    return mask::isneg();
  }
}

Positive Coq_Pos::sub(const Positive &x, const Positive &y) {
  auto &&_sv = sub_mask(x, y);
  if (std::holds_alternative<typename Coq_Pos::mask::IsPos>(_sv.v())) {
    const auto &[a0] = std::get<typename Coq_Pos::mask::IsPos>(_sv.v());
    return a0;
  } else {
    return Positive::xh();
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

Positive Coq_Pos::div2(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return *a0;
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return *a0;
  } else {
    return Positive::xh();
  }
}

Positive Coq_Pos::div2_up(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return succ(*a0);
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return *a0;
  } else {
    return Positive::xh();
  }
}

Comparison Coq_Pos::compare_cont(Comparison r, const Positive &x,
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

Comparison Coq_Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

bool Coq_Pos::eqb(const Positive &p, const Positive &q) {
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

bool Coq_Pos::leb(const Positive &x, const Positive &y) {
  switch (compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

std::pair<Positive, Coq_Pos::mask> Coq_Pos::sqrtrem(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    const Positive &a0_value = *a0;
    if (std::holds_alternative<typename Positive::XI>(a0_value.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(a0_value.v());
      const Positive &a00_value = *a00;
      return sqrtrem_step([](const Positive &x) { return Positive::xi(x); },
                          [](const Positive &x) { return Positive::xi(x); },
                          sqrtrem(a00_value));
    } else if (std::holds_alternative<typename Positive::XO>(a0_value.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(a0_value.v());
      const Positive &a00_value = *a00;
      return sqrtrem_step([](const Positive &x) { return Positive::xo(x); },
                          [](const Positive &x) { return Positive::xi(x); },
                          sqrtrem(a00_value));
    } else {
      return std::make_pair(Positive::xh(),
                            mask::ispos(Positive::xo(Positive::xh())));
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    const Positive &a0_value = *a0;
    if (std::holds_alternative<typename Positive::XI>(a0_value.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(a0_value.v());
      const Positive &a00_value = *a00;
      return sqrtrem_step([](const Positive &x) { return Positive::xi(x); },
                          [](const Positive &x) { return Positive::xo(x); },
                          sqrtrem(a00_value));
    } else if (std::holds_alternative<typename Positive::XO>(a0_value.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(a0_value.v());
      const Positive &a00_value = *a00;
      return sqrtrem_step([](const Positive &x) { return Positive::xo(x); },
                          [](const Positive &x) { return Positive::xo(x); },
                          sqrtrem(a00_value));
    } else {
      return std::make_pair(Positive::xh(), mask::ispos(Positive::xh()));
    }
  } else {
    return std::make_pair(Positive::xh(), mask::isnul());
  }
}

Positive Coq_Pos::sqrt(const Positive &p) { return sqrtrem(p).first; }

N Coq_Pos::Nsucc_double(const N &x) {
  if (std::holds_alternative<typename N::N0>(x.v())) {
    return N::npos(Positive::xh());
  } else {
    const auto &[a0] = std::get<typename N::Npos>(x.v());
    return N::npos(Positive::xi(a0));
  }
}

N Coq_Pos::Ndouble(const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return N::npos(Positive::xo(a0));
  }
}

Positive Coq_Pos::lor(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Positive::xi(lor(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Positive::xi(lor(*a0, *a00));
    } else {
      return p;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Positive::xi(lor(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Positive::xo(lor(*a0, *a00));
    } else {
      return Positive::xi(*a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Positive::xi(*a00);
    } else {
      return q;
    }
  }
}

N Coq_Pos::land(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Nsucc_double(land(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Ndouble(land(*a0, *a00));
    } else {
      return N::npos(Positive::xh());
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Ndouble(land(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Ndouble(land(*a0, *a00));
    } else {
      return N::n0();
    }
  } else {
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      return N::n0();
    } else {
      return N::npos(Positive::xh());
    }
  }
}

N Coq_Pos::ldiff(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Ndouble(ldiff(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Nsucc_double(ldiff(*a0, *a00));
    } else {
      return N::npos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Ndouble(ldiff(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Ndouble(ldiff(*a0, *a00));
    } else {
      return N::npos(p);
    }
  } else {
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      return N::npos(Positive::xh());
    } else {
      return N::n0();
    }
  }
}

N Coq_Pos::lxor(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Ndouble(lxor(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Nsucc_double(lxor(*a0, *a00));
    } else {
      return N::npos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return Nsucc_double(lxor(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return Ndouble(lxor(*a0, *a00));
    } else {
      return N::npos(Positive::xi(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return N::npos(Positive::xo(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return N::npos(Positive::xi(*a00));
    } else {
      return N::n0();
    }
  }
}

uint64_t Coq_Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, x,
      UINT64_C(1));
}

Positive Coq_Pos::of_succ_nat(uint64_t n) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    uint64_t x = n - 1;
    return succ(of_succ_nat(x));
  }
}

Positive Coq_Pos::pred(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(*a0);
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return pred_double(*a0);
  } else {
    return Positive::xh();
  }
}

Positive Coq_Pos::pow(const Positive &x, Positive x0_) {
  return iter<Positive>([=](Positive _x0) -> Positive { return mul(x, _x0); },
                        Positive::xh(), std::move(x0_));
}

Positive Coq_Pos::square(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return Positive::xi(Positive::xo(add(square(*a0), *a0)));
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return Positive::xo(Positive::xo(square(*a0)));
  } else {
    return Positive::xh();
  }
}

uint64_t Coq_Pos::size_nat(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return (size_nat(*a0) + 1);
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return (size_nat(*a0) + 1);
  } else {
    return UINT64_C(1);
  }
}

Positive Coq_Pos::size(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return succ(size(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return succ(size(*a0));
  } else {
    return Positive::xh();
  }
}

Positive Coq_Pos::min(Positive p, Positive p_) {
  switch (compare(p, p_)) {
  case Comparison::GT: {
    return p_;
  }
  default: {
    return p;
  }
  }
}

Positive Coq_Pos::max(Positive p, Positive p_) {
  switch (compare(p, p_)) {
  case Comparison::GT: {
    return p;
  }
  default: {
    return p_;
  }
  }
}

bool Coq_Pos::ltb(const Positive &x, const Positive &y) {
  switch (compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

Positive Coq_Pos::gcdn(uint64_t n, const Positive &a, const Positive &b) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    uint64_t n0 = n - 1;
    if (std::holds_alternative<typename Positive::XI>(a.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(a.v());
      if (std::holds_alternative<typename Positive::XI>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XI>(b.v());
        switch (compare(*a0, *a00)) {
        case Comparison::EQ: {
          return a;
        }
        case Comparison::LT: {
          return gcdn(n0, sub(*a00, *a0), a);
        }
        case Comparison::GT: {
          return gcdn(n0, sub(*a0, *a00), b);
        }
        default:
          std::unreachable();
        }
      } else if (std::holds_alternative<typename Positive::XO>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(b.v());
        return gcdn(n0, a, *a00);
      } else {
        return Positive::xh();
      }
    } else if (std::holds_alternative<typename Positive::XO>(a.v())) {
      const auto &[a1] = std::get<typename Positive::XO>(a.v());
      if (std::holds_alternative<typename Positive::XI>(b.v())) {
        return gcdn(n0, *a1, b);
      } else if (std::holds_alternative<typename Positive::XO>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(b.v());
        return Positive::xo(gcdn(n0, *a1, *a00));
      } else {
        return Positive::xh();
      }
    } else {
      return Positive::xh();
    }
  }
}

Positive Coq_Pos::gcd(const Positive &a, const Positive &b) {
  return gcdn((size_nat(a) + size_nat(b)), a, b);
}

std::pair<Positive, std::pair<Positive, Positive>>
Coq_Pos::ggcdn(uint64_t n, const Positive &a, const Positive &b) {
  if (n <= 0) {
    return std::make_pair(Positive::xh(), std::make_pair(a, b));
  } else {
    uint64_t n0 = n - 1;
    if (std::holds_alternative<typename Positive::XI>(a.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(a.v());
      if (std::holds_alternative<typename Positive::XI>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XI>(b.v());
        switch (compare(*a0, *a00)) {
        case Comparison::EQ: {
          return std::make_pair(a,
                                std::make_pair(Positive::xh(), Positive::xh()));
        }
        case Comparison::LT: {
          auto [g, p] = ggcdn(n0, sub(*a00, *a0), a);
          auto [ba, aa] = std::move(p);
          return std::make_pair(
              std::move(g),
              std::make_pair(aa, add(aa, Positive::xo(std::move(ba)))));
          break;
        }
        case Comparison::GT: {
          auto [g, p] = ggcdn(n0, sub(*a0, *a00), b);
          auto [ab, bb] = std::move(p);
          return std::make_pair(
              std::move(g),
              std::make_pair(add(bb, Positive::xo(std::move(ab))), bb));
          break;
        }
        default:
          std::unreachable();
        }
      } else if (std::holds_alternative<typename Positive::XO>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(b.v());
        auto [g, p] = ggcdn(n0, a, *a00);
        auto [aa, bb] = std::move(p);
        return std::make_pair(
            std::move(g),
            std::make_pair(std::move(aa), Positive::xo(std::move(bb))));
      } else {
        return std::make_pair(Positive::xh(),
                              std::make_pair(a, Positive::xh()));
      }
    } else if (std::holds_alternative<typename Positive::XO>(a.v())) {
      const auto &[a1] = std::get<typename Positive::XO>(a.v());
      if (std::holds_alternative<typename Positive::XI>(b.v())) {
        auto [g, p] = ggcdn(n0, *a1, b);
        auto [aa, bb] = std::move(p);
        return std::make_pair(
            std::move(g),
            std::make_pair(Positive::xo(std::move(aa)), std::move(bb)));
      } else if (std::holds_alternative<typename Positive::XO>(b.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(b.v());
        auto [g, p] = ggcdn(n0, *a1, *a00);
        return std::make_pair(Positive::xo(std::move(g)), std::move(p));
      } else {
        return std::make_pair(Positive::xh(),
                              std::make_pair(a, Positive::xh()));
      }
    } else {
      return std::make_pair(Positive::xh(), std::make_pair(Positive::xh(), b));
    }
  }
}

std::pair<Positive, std::pair<Positive, Positive>>
Coq_Pos::ggcd(const Positive &a, const Positive &b) {
  return ggcdn((size_nat(a) + size_nat(b)), a, b);
}

Positive Coq_Pos::shiftl_nat(Positive p, uint64_t n) {
  if (n <= 0) {
    return p;
  } else {
    uint64_t n0 = n - 1;
    return Positive::xo(shiftl_nat(std::move(p), n0));
  }
}

Positive Coq_Pos::shiftr_nat(Positive p, uint64_t n) {
  if (n <= 0) {
    return p;
  } else {
    uint64_t n0 = n - 1;
    return div2(shiftr_nat(std::move(p), n0));
  }
}

Positive Coq_Pos::shiftl(Positive p, const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return p;
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return iter<Positive>([](const Positive &x) { return Positive::xo(x); },
                          std::move(p), a0);
  }
}

Positive Coq_Pos::shiftr(Positive p, const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return p;
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return iter<Positive>(div2, std::move(p), a0);
  }
}

bool Coq_Pos::testbit_nat(const Positive &p, uint64_t n) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (n <= 0) {
      return true;
    } else {
      uint64_t n_ = n - 1;
      return testbit_nat(*a0, n_);
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (n <= 0) {
      return false;
    } else {
      uint64_t n_ = n - 1;
      return testbit_nat(*a0, n_);
    }
  } else {
    if (n <= 0) {
      return true;
    } else {
      uint64_t _x = n - 1;
      return false;
    }
  }
}

bool Coq_Pos::testbit(const Positive &p, const N &n) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename N::N0>(n.v())) {
      return true;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(n.v());
      return testbit(*a0, pred_N(a00));
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename N::N0>(n.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(n.v());
      return testbit(*a0, pred_N(a00));
    }
  } else {
    if (std::holds_alternative<typename N::N0>(n.v())) {
      return true;
    } else {
      return false;
    }
  }
}

Positive Coq_Pos::of_nat(uint64_t n) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    uint64_t x = n - 1;
    if (x <= 0) {
      return Positive::xh();
    } else {
      uint64_t _x = x - 1;
      return succ(of_nat(x));
    }
  }
}

Positive Coq_Pos::of_uint_acc(const Uint &d, Positive acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return of_uint_acc(
        *a0, mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                 std::move(acc)));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xh(),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xo(Positive::xh()),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xi(Positive::xh()),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xo(Positive::xo(Positive::xh())),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xi(Positive::xo(Positive::xh())),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xo(Positive::xi(Positive::xh())),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xi(Positive::xi(Positive::xh())),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xo(Positive::xo(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return of_uint_acc(
        *a0, add(Positive::xi(Positive::xo(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                     std::move(acc))));
  }
}

N Coq_Pos::of_uint(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return N::n0();
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return of_uint(*a0);
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return N::npos(of_uint_acc(*a0, Positive::xh()));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return N::npos(of_uint_acc(*a0, Positive::xo(Positive::xh())));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return N::npos(of_uint_acc(*a0, Positive::xi(Positive::xh())));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return N::npos(
        of_uint_acc(*a0, Positive::xo(Positive::xo(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return N::npos(
        of_uint_acc(*a0, Positive::xi(Positive::xo(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return N::npos(
        of_uint_acc(*a0, Positive::xo(Positive::xi(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return N::npos(
        of_uint_acc(*a0, Positive::xi(Positive::xi(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return N::npos(of_uint_acc(
        *a0, Positive::xo(Positive::xo(Positive::xo(Positive::xh())))));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return N::npos(of_uint_acc(
        *a0, Positive::xi(Positive::xo(Positive::xo(Positive::xh())))));
  }
}

Positive Coq_Pos::of_hex_uint_acc(const Uint0 &d, Positive acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return of_hex_uint_acc(*a0, mul(Positive::xo(Positive::xo(Positive::xo(
                                        Positive::xo(Positive::xh())))),
                                    std::move(acc)));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xh(), mul(Positive::xo(Positive::xo(Positive::xo(
                                         Positive::xo(Positive::xh())))),
                                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xo(Positive::xh()),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xi(Positive::xh()),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xo(Positive::xo(Positive::xh())),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xi(Positive::xo(Positive::xh())),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xo(Positive::xi(Positive::xh())),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return of_hex_uint_acc(*a0, add(Positive::xi(Positive::xi(Positive::xh())),
                                    mul(Positive::xo(Positive::xo(Positive::xo(
                                            Positive::xo(Positive::xh())))),
                                        std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xo(Positive::xo(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xi(Positive::xo(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xi(Positive::xi(Positive::xo(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xo(Positive::xo(Positive::xi(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xi(Positive::xo(Positive::xi(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xo(Positive::xi(Positive::xi(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return of_hex_uint_acc(
        *a0, add(Positive::xi(Positive::xi(Positive::xi(Positive::xh()))),
                 mul(Positive::xo(Positive::xo(
                         Positive::xo(Positive::xo(Positive::xh())))),
                     std::move(acc))));
  }
}

N Coq_Pos::of_hex_uint(const Uint0 &d) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return N::n0();
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return of_hex_uint(*a0);
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return N::npos(of_hex_uint_acc(*a0, Positive::xh()));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return N::npos(of_hex_uint_acc(*a0, Positive::xo(Positive::xh())));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return N::npos(of_hex_uint_acc(*a0, Positive::xi(Positive::xh())));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return N::npos(
        of_hex_uint_acc(*a0, Positive::xo(Positive::xo(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return N::npos(
        of_hex_uint_acc(*a0, Positive::xi(Positive::xo(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return N::npos(
        of_hex_uint_acc(*a0, Positive::xo(Positive::xi(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return N::npos(
        of_hex_uint_acc(*a0, Positive::xi(Positive::xi(Positive::xh()))));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xo(Positive::xo(Positive::xo(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xi(Positive::xo(Positive::xo(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xi(Positive::xi(Positive::xo(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xo(Positive::xo(Positive::xi(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xi(Positive::xo(Positive::xi(Positive::xh())))));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xo(Positive::xi(Positive::xi(Positive::xh())))));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return N::npos(of_hex_uint_acc(
        *a0, Positive::xi(Positive::xi(Positive::xi(Positive::xh())))));
  }
}

N Coq_Pos::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return of_hex_uint(u);
  }
}

std::optional<Positive> Coq_Pos::of_int(const Signed_int &d) {
  if (std::holds_alternative<typename Signed_int::Pos>(d.v())) {
    const auto &[d1] = std::get<typename Signed_int::Pos>(d.v());
    auto &&_sv0 = of_uint(d1);
    if (std::holds_alternative<typename N::N0>(_sv0.v())) {
      return std::optional<Positive>();
    } else {
      const auto &[a00] = std::get<typename N::Npos>(_sv0.v());
      return std::make_optional<Positive>(a00);
    }
  } else {
    return std::optional<Positive>();
  }
}

std::optional<Positive> Coq_Pos::of_hex_int(const Signed_int0 &d) {
  if (std::holds_alternative<typename Signed_int0::Pos0>(d.v())) {
    const auto &[d1] = std::get<typename Signed_int0::Pos0>(d.v());
    auto &&_sv0 = of_hex_uint(d1);
    if (std::holds_alternative<typename N::N0>(_sv0.v())) {
      return std::optional<Positive>();
    } else {
      const auto &[a00] = std::get<typename N::Npos>(_sv0.v());
      return std::make_optional<Positive>(a00);
    }
  } else {
    return std::optional<Positive>();
  }
}

std::optional<Positive> Coq_Pos::of_num_int(const Signed_int1 &d) {
  if (std::holds_alternative<typename Signed_int1::IntDecimal>(d.v())) {
    const auto &[i] = std::get<typename Signed_int1::IntDecimal>(d.v());
    return of_int(i);
  } else {
    const auto &[i] = std::get<typename Signed_int1::IntHexadecimal>(d.v());
    return of_hex_int(i);
  }
}

Uint Coq_Pos::to_little_uint(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return Little::succ_double(to_little_uint(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return Little::double_(to_little_uint(*a0));
  } else {
    return Uint::d1(Uint::nil());
  }
}

Uint Coq_Pos::to_uint(const Positive &p) { return to_little_uint(p).rev(); }

Uint0 Coq_Pos::to_little_hex_uint(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return Coq_Little::succ_double(to_little_hex_uint(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return Coq_Little::double_(to_little_hex_uint(*a0));
  } else {
    return Uint0::d11(Uint0::nil0());
  }
}

Uint0 Coq_Pos::to_hex_uint(const Positive &p) {
  return to_little_hex_uint(p).rev0();
}

Uint1 Coq_Pos::to_num_uint(const Positive &p) {
  return Uint1::uintdecimal(to_uint(p));
}

Uint1 Coq_Pos::to_num_hex_uint(const Positive &n) {
  return Uint1::uinthexadecimal(to_hex_uint(n));
}

Signed_int Coq_Pos::to_int(const Positive &n) {
  return Signed_int::pos(to_uint(n));
}

Signed_int0 Coq_Pos::to_hex_int(const Positive &p) {
  return Signed_int0::pos0(to_hex_uint(p));
}

Signed_int1 Coq_Pos::to_num_int(const Positive &n) {
  return Signed_int1::intdecimal(to_int(n));
}

Signed_int1 Coq_Pos::to_num_hex_int(const Positive &n) {
  return Signed_int1::inthexadecimal(to_hex_int(n));
}

bool Coq_Pos::eq_dec(const Positive &p, const Positive &x0) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(x0.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(x0.v());
      if (eq_dec(*a0, *a00)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XO>(x0.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(x0.v());
      if (eq_dec(*a0, *a00)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(x0.v())) {
      return true;
    } else {
      return false;
    }
  }
}

Coq_Pos::PeanoView Coq_Pos::peanoView(const Positive &p) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    return peanoView(*a0).peanoView_xI(*a0);
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    return peanoView(*a0).peanoView_xO(*a0);
  } else {
    return PeanoView::peanoone();
  }
}

Reflect Coq_Pos::eqb_spec(const Positive &x, const Positive &y) {
  return Bool::iff_reflect(eqb(x, y));
}

Comparison Coq_Pos::switch_Eq(Comparison c, Comparison c_) {
  switch (c_) {
  case Comparison::EQ: {
    return c;
  }
  case Comparison::LT: {
    return Comparison::LT;
  }
  case Comparison::GT: {
    return Comparison::GT;
  }
  default:
    std::unreachable();
  }
}

Reflect Coq_Pos::leb_spec0(const Positive &x, const Positive &y) {
  return Bool::iff_reflect(leb(x, y));
}

Reflect Coq_Pos::ltb_spec0(const Positive &x, const Positive &y) {
  return Bool::iff_reflect(ltb(x, y));
}

bool Coq_Pos::Private_Dec::max_dec(Positive n, Positive m0) {
  return max_case<bool>(
      std::move(n), std::move(m0),
      [](Positive, Positive, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool Coq_Pos::Private_Dec::min_dec(Positive n, Positive m0) {
  return min_case<bool>(
      std::move(n), std::move(m0),
      [](Positive, Positive, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool Coq_Pos::max_dec(const Positive &x0_, const Positive &x1_) {
  return Private_Dec::max_dec(x0_, x1_);
}

bool Coq_Pos::min_dec(const Positive &x0_, const Positive &x1_) {
  return Private_Dec::min_dec(x0_, x1_);
}

Compare<Positive> Positive_as_OT::compare(const Positive &x,
                                          const Positive &y) {
  switch (Coq_Pos::compare(x, y)) {
  case Comparison::EQ: {
    return Compare<Positive>::eq();
  }
  case Comparison::LT: {
    return Compare<Positive>::lt();
  }
  case Comparison::GT: {
    return Compare<Positive>::gt();
  }
  default:
    std::unreachable();
  }
}

bool Positive_as_OT::eq_dec(const Positive &x0_, const Positive &x1_) {
  return Coq_Pos::eq_dec(x0_, x1_);
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
