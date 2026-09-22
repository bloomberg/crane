#include "template_merge_outlined_member.h"

bool PeanoNat::eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::eqb(*a0, *a00);
    }
  }
}

Nat Tally::bump(Nat n) { return Nat::s(std::move(n)); }

Box<Nat> roundtrip(Box<Nat> x) { return x; }

bool sz_is(const Box<Nat> &b, const Nat &n) {
  return PeanoNat::eqb(b.size(), n);
}

Box<Nat> round(const Box<Nat> &x0_) { return roundtrip(x0_); }
