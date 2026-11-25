#pragma once

#include "fn.h"
#include <cstdint>

/// A sig whose payload is a function, passed as a parameter (so its C++ type
/// is the concrete Sig<std::function<uint64_t(uint64_t)>>), must be applied
/// directly rather than through an erased-function cast.
struct SigFunParamResultCast {
  static uint64_t apply_sig(const crane::fn<uint64_t(uint64_t)> &x0_,
                            uint64_t x1_);
  static inline const crane::fn<uint64_t(uint64_t)> idf =
      [](uint64_t n) { return n; };
  static inline const uint64_t go = apply_sig(idf, UINT64_C(2));
};
