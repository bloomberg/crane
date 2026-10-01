#include "member_calls_later.h"

bool PeanoNat::leb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return true;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::leb(*a0, *a00);
    }
  }
}

Nat Helper::pick(Nat a, Nat b) {
  if (PeanoNat::leb(a, b)) {
    return b;
  } else {
    return a;
  }
}
