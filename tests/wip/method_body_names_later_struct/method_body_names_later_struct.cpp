#include "method_body_names_later_struct.h"

Comparison PeanoNat::compare(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::compare(*a0, *a00);
    }
  }
}

Zed Arith::roundtrip(Zed x) { return x; }

Comparison Arith::norm(Comparison c) { return c; }

bool le(const Zed &x0_, const Zed &x1_) { return x0_.le_dec(x1_); }

Zed round(const Zed &x0_) { return Arith::roundtrip(x0_); }
