#include "nested_owner_two_template_heads.h"

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

bool PeanoNat::even(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return true;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename Nat::O>(_sv0.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(_sv0.v());
      return PeanoNat::even(*a00);
    }
  }
}

bool PeanoNat::odd(const Nat &n) { return !(PeanoNat::even(n)); }

Nat Tally::bump(Nat n) { return Nat::s(std::move(n)); }

Bag::bag<Nat> roundtrip(Bag::bag<Nat> b) { return b; }

bool count_odd_is(const Bag::bag<Nat> &b, const Nat &n) {
  return PeanoNat::eqb(b.countIf(PeanoNat::odd), n);
}

Bag::bag<Nat> round(const Bag::bag<Nat> &x0_) { return roundtrip(x0_); }
