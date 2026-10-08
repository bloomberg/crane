#include "shared_variant_constant.h"

Positive Pos::succ(const Positive &x) {
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    return Positive::xi(*a0);
  } else {
    return pos_2;
  }
}

Positive Pos::add(const Positive &x, const Positive &y) {
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xo(add(*a0, *a00));
    } else {
      return Positive::xi(*a0);
    }
  } else {
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xo(succ(*a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xi(*a00);
    } else {
      return pos_2;
    }
  }
}

Positive Pos::add_carry(const Positive &x, const Positive &y) {
  static const auto pos_3 = crane::immortal(Positive::xi(Positive::xh()));
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xi(add_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else {
      return Positive::xi(succ(*a0));
    }
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else {
    if (crane::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XI>(y.v());
      return Positive::xi(succ(*a00));
    } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = crane::get<typename Positive::XO>(y.v());
      return Positive::xo(succ(*a00));
    } else {
      return pos_3;
    }
  }
}

Positive SharedVariantConstant::seven(std::monostate) {
  static const auto pos_7 =
      crane::immortal(Positive::xi(Positive::xi(Positive::xh())));
  return pos_7;
}

std::pair<Positive, Positive> SharedVariantConstant::pair_of(std::monostate) {
  static const auto pos_12 =
      crane::immortal(Positive::xo(Positive::xo(Positive::xi(Positive::xh()))));
  static const auto pos_6 =
      crane::immortal(Positive::xo(Positive::xi(Positive::xh())));
  return std::make_pair(pos_6, pos_12);
}

Positive SharedVariantConstant::add_ten(const Positive &p) {
  static const auto pos_10 =
      crane::immortal(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))));
  return Pos::add(p, pos_10);
}

Positive SharedVariantConstant::sum_tens(uint64_t n, Positive acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t m = n - 1;
    return sum_tens(m, add_ten(std::move(acc)));
  }
}

/// 2^110: a constant nested deeper than a compiler parses, whose
/// initialiser is split into bindings that run once.
Positive SharedVariantConstant::huge(std::monostate) {
  static const auto pos = []() {
    auto _lit0 = Positive::xo(Positive::xo(Positive::xo(Positive::xo(
        Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
            Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                    Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                        Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                            Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                                Positive::xh()))))))))))))))))))))))))))))));
    auto _lit1 = Positive::xo(Positive::xo(Positive::xo(Positive::xo(
        Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
            Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                    Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                        Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                            Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                                std::move(_lit0)))))))))))))))))))))))))))))));
    auto _lit2 = Positive::xo(Positive::xo(Positive::xo(Positive::xo(
        Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
            Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                    Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                        Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                            Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                                std::move(_lit1)))))))))))))))))))))))))))))));
    return crane::immortal(Positive::xo(
        Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
            Positive::xo(Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                    Positive::xo(Positive::xo(Positive::xo(Positive::xo(
                        Positive::xo(std::move(_lit2))))))))))))))))))))));
  }();
  return pos;
}

/// A constant that is no numeral is named k; so is the parameter, read
/// last -- and so moved -- where the constant is built.
std::pair<List<Positive>, List<Positive>>
SharedVariantConstant::with_k(const List<Positive> &k) {
  static const auto k_1 = crane::immortal(List<Positive>::cons(
      Positive::xi(Positive::xh()),
      List<Positive>::cons(Positive::xi(Positive::xo(Positive::xh())),
                           List<Positive>::nil())));
  return std::make_pair(k, k_1);
}
