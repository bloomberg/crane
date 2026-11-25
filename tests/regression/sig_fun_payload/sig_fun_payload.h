#pragma once

#include "fn.h"
#include <cstdint>

struct SigFunPayload {
  static inline const crane::fn<uint64_t(uint64_t)> mk =
      [](uint64_t x) { return (x + UINT64_C(1)); };
  static inline const uint64_t go = mk(UINT64_C(4));
};
