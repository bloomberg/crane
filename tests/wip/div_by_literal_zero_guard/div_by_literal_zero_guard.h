#pragma once

#include <cstdint>

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.div 0 0 in a polymorphic definition is not folded and prints
/// (0 ? 0 / 0 : 0); the dead 0 / 0 is rejected by clang's
/// -Wdivision-by-zero under the suite's -Werror.  The value is right.
struct DivByLiteralZeroGuard {
  template <typename T1> static uint64_t f(const T1 &) {
    return ((UINT64_C(0) ? UINT64_C(0) / UINT64_C(0) : 0) +
            (UINT64_C(0) ? UINT64_C(5) % UINT64_C(0) : UINT64_C(5)));
  }

  static inline const uint64_t t = f<bool>(true);
};
