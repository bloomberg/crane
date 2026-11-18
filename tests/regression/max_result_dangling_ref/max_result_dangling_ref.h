#pragma once

#include <algorithm>
#include <cstdint>

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
struct MaxResultDanglingRef {
  static uint64_t f(uint64_t a, uint64_t b);
  static uint64_t g(uint64_t a, uint64_t b);
};
