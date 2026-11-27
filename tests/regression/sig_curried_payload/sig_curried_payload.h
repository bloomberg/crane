#pragma once

#include "fn.h"
#include <cstdint>

struct SigCurriedPayload {
  static inline const crane::fn<uint64_t(uint64_t, uint64_t)> mk =
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return _x0 + _x1; };
  static inline const uint64_t go = mk(UINT64_C(1), UINT64_C(2));
};
