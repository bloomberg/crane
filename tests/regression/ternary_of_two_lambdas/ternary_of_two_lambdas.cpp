#include "ternary_of_two_lambdas.h"

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

Nat f_even(const Nat &x0_, const Nat &x1_) { return x0_.add(x1_); }

Nat f_odd(const Nat &x0_, const Nat &x1_) { return x0_.mul(x1_); }

/// Point-free: the body is an if whose branches are functions, and no
/// argument is written.
Nat pick(const Nat &n, Nat x0_) {
  if (PeanoNat::even(n)) {
    return f_even(n, std::move(x0_));
  } else {
    return f_odd(n, std::move(x0_));
  }
}

Nat go(const Nat &x0_, const Nat &x1_) { return pick(x0_, x1_); }
