#include "typed_fit_scrutinee_let.h"

Positive Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(crane::shared_child(a0));
  } else {
    return Positive::xo(Positive::xh());
  }
}

Positive Pos::of_succ_nat(uint64_t n) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    uint64_t x = n - 1;
    return succ(of_succ_nat(x));
  }
}

Z BinInt::of_nat(uint64_t n) {
  if (n <= 0) {
    return Z::z0();
  } else {
    uint64_t n0 = n - 1;
    return Z::zpos(Pos::of_succ_nat(n0));
  }
}

uint64_t TypedFitScrutineeLet::on_t3(bool b, uint64_t n) {
  auto &&_sv = [&]() -> TypedFitScrutineeLet::t3 {
    if (b) {
      return t3::a();
    } else {
      uint64_t k = n + UINT64_C(1);
      return t3::b(k);
    }
  }();
  if (std::holds_alternative<typename TypedFitScrutineeLet::t3::A>(_sv.v())) {
    return UINT64_C(0);
  } else {
    return UINT64_C(1);
  }
}

uint64_t TypedFitScrutineeLet::on_z(bool b, uint64_t n) {
  auto &&_sv = [&]() -> Z {
    if (b) {
      return Z::z0();
    } else {
      uint64_t k = n + UINT64_C(1);
      return BinInt::of_nat(k);
    }
  }();
  if (std::holds_alternative<typename Z::Z0>(_sv.v())) {
    return UINT64_C(0);
  } else {
    return UINT64_C(1);
  }
}
