#ifndef INCLUDED_DEEP_ARITH_NESTING
#define INCLUDED_DEEP_ARITH_NESTING

#include <cstdint>
#include <utility>

struct DeepArithNesting {
  /// 1200 additions: deeper than clang's 1024-bracket limit.
  static uint64_t bump(uint64_t x);
  static constexpr uint64_t answer = UINT64_C(1200);
};

#endif // INCLUDED_DEEP_ARITH_NESTING
