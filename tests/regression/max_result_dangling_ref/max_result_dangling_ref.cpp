#include "max_result_dangling_ref.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.pred (Nat.max a b) lowers to auto &&_once1 = std::max(x, y);:
/// std::max returns a reference to one of its temporaries, which dies at
/// the end of the full-expression, so the reads of _once1 are use after
/// free (clang's -Wdangling rejects it under -Werror).
///
/// g: Nat.modulo a (Nat.max b 1): the % mapping reads its divisor
/// twice and bound std::max(b, 1) with auto&& the same way.
uint64_t MaxResultDanglingRef::f(uint64_t a, uint64_t b) {
  auto _once1 = std::max((a + UINT64_C(1)), (b + UINT64_C(2)));
  return (_once1 ? _once1 - 1 : _once1);
}

uint64_t MaxResultDanglingRef::g(uint64_t a, uint64_t b) {
  auto _once1 = std::max(b, UINT64_C(1));
  return (_once1 ? a % _once1 : a);
}
