#include "shared_variant_constant.h"

Positive Pos::succ(const Positive &x) {
  if (crane::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = crane::get<typename Positive::XO>(x.v());
    return Positive::xi(*a0);
  } else {
    return crane::constant([]() { return Positive::xo(Positive::xh()); });
  }
}

Positive Pos::add(const Positive &x, const Positive &y) {
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
      return crane::constant([]() { return Positive::xo(Positive::xh()); });
    }
  }
}

Positive Pos::add_carry(const Positive &x, const Positive &y) {
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
      return crane::constant([]() { return Positive::xi(Positive::xh()); });
    }
  }
}

Positive SharedVariantConstant::seven(std::monostate) {
  return crane::constant(
      []() { return Positive::xi(Positive::xi(Positive::xh())); });
}

std::pair<Positive, Positive> SharedVariantConstant::pair_of(std::monostate) {
  return std::make_pair(
      crane::constant(
          []() { return Positive::xo(Positive::xi(Positive::xh())); }),
      crane::constant([]() {
        return Positive::xo(Positive::xo(Positive::xi(Positive::xh())));
      }));
}

Positive SharedVariantConstant::add_ten(const Positive &p) {
  return Pos::add(p, crane::constant([]() {
                    return Positive::xo(
                        Positive::xi(Positive::xo(Positive::xh())));
                  }));
}

Positive SharedVariantConstant::sum_tens(uint64_t n, Positive acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t m = n - 1;
    return sum_tens(m, add_ten(std::move(acc)));
  }
}
