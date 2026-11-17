#pragma once

#include <cstdint>

struct ModuleNamedCrane {
  struct crane_ {
    static constexpr uint64_t x = UINT64_C(2);
  };

  static inline const uint64_t go = crane_::x;
};
