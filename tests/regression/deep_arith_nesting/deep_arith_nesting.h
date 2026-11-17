#pragma once

#include <cstdint>
#include <utility>

struct DeepArithNesting {
  /// 1200 additions: deeper than clang's 1024-bracket limit.
  static uint64_t bump(uint64_t x);
  static inline const uint64_t answer = bump(UINT64_C(0));
};
