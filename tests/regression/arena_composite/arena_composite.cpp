#include "arena_composite.h"

Bool0 PeanoNat::leb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return Bool0::TRUE_;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return Bool0::FALSE_;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::leb(*a0, *a00);
    }
  }
}

Bool0 PeanoNat::ltb(const Nat &n, const Nat &m) {
  return PeanoNat::leb(Nat::s(n), m);
}

Nat PeanoNat::max(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return m;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return n;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return Nat::s(PeanoNat::max(*a0, *a00));
    }
  }
}
