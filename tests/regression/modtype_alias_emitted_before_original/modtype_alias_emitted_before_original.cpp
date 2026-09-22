#include "modtype_alias_emitted_before_original.h"

bool PeanoNat::eq_dec(const Nat &n, const Nat &m) {
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
      bool s = PeanoNat::eq_dec(*a0, *a00);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool NatDec::eq_dec(NatDec::t x0_, NatDec::t x1_) {
  return PeanoNat::eq_dec(std::move(x0_), std::move(x1_));
}

bool go(const Nat &x0_, const Nat &x1_) { return MN::same(x0_, x1_); }
