#include "div_by_literal_zero_guard.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.div 0 0 in a polymorphic definition is not folded and prints
/// (0 ? 0 / 0 : 0); the dead 0 / 0 is rejected by clang's
/// -Wdivision-by-zero under the suite's -Werror.  The value is right.
/// A literal Nat.modulo 12 0 in a branch of a mutual fixpoint, which is
/// not polymorphic.
uint64_t DivByLiteralZeroGuard::ev(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(12);
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return od(*a1);
  }
}

uint64_t DivByLiteralZeroGuard::od(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return ev(*a1);
  }
}
