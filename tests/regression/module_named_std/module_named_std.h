#pragma once

#include <cstdint>

struct ModuleNamedStd {
  struct std_ {
    static constexpr uint64_t x = UINT64_C(1);
  };

  static inline const uint64_t go = std_::x;
};
