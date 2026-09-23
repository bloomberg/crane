#include "erased_arg_callable_spelled_std_function.h"

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

bool PeanoNat::ltb(Nat n, const Nat &m) {
  return PeanoNat::leb(Nat::s(std::move(n)), m);
}

bool small_dec(const Nat &n) {
  return Bool::bool_dec(
      PeanoNat::ltb(n, Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                           Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))))),
      true);
}

/// The call site that fails: a lambda passed where deduction runs.
bool allsmall(const List<Nat> &l) {
  if (forall_dec(l, [](const Nat &a) { return small_dec(a); })) {
    return true;
  } else {
    return false;
  }
}

bool Bool::bool_dec(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}
